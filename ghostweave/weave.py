"""Weaving P2 into P1 as ghost code.

Soundness rests on two facts.

(1) Erasure: every statement taken from P2 (and every scheduling statement) assigns only ghost
    variables, which Dafny's ghost type system checks.  Erasing the ghost code gives P1 exactly.

(2) Step lemma: for any loop W = `while c { B }` and any finite sequence of guarded steps
    `if g_i && c { B }`, with the g_i arbitrary (they may read real state, ghost counters, or prophecy
    values),
        if g_1 && c {B}; ...; if g_n && c {B}; while c {B}   ==   while c {B}
    so a loop of P2 can be split into steps placed anywhere in P1, provided that at the end either
    the remaining loop is executed (`rest`) or `!c` is asserted (`assert`, the "ghost pc reached the
    end" obligation).  The same holds for an `if` of P2 whose branches are woven under a snapshot of
    its condition.  So the projection of the woven program onto P2's variables is P2, for every
    choice of schedule.

The *plan* chooses the schedule (that choice is the alignment); the plan can never affect soundness.
"""
from __future__ import annotations
import copy
import itertools
from dataclasses import dataclass, field
from .ir import *


def has_loop(ss):
    return count_loops(ss) > 0


def top_items(ss):
    """indices of top-level statements that contain loops (While, or If containing loops)."""
    return [k for k, s in enumerate(ss) if isinstance(s, While) or (isinstance(s, If) and has_loop(s.th + s.el))]


def mark_ghost(ss):
    for s in ss:
        s.ghost = True
        if isinstance(s, If):
            mark_ghost(s.th); mark_ghost(s.el)
        elif isinstance(s, While):
            mark_ghost(s.body)
    return ss


def label_loops(ss, prefix, ctr):
    for s in ss:
        if isinstance(s, While):
            s.lid = f'{prefix}{ctr[0]}'
            ctr[0] += 1
            label_loops(s.body, prefix, ctr)
        elif isinstance(s, If):
            label_loops(s.th, prefix, ctr); label_loops(s.el, prefix, ctr)


def find_loop(ss, lid):
    for s in ss:
        if isinstance(s, While):
            if s.lid == lid:
                return s
            r = find_loop(s.body, lid)
            if r:
                return r
        elif isinstance(s, If):
            r = find_loop(s.th, lid) or find_loop(s.el, lid)
            if r:
                return r
    return None


def if_conditions(ss, acc=None):
    if acc is None:
        acc = []
    for s in ss:
        if isinstance(s, If):
            acc.append(s.c)
            if_conditions(s.th, acc); if_conditions(s.el, acc)
    return acc


# ------------------------------------------------------------------ plans
@dataclass
class LoopPlan:
    place: str = 'end'        # end | begin | nested
    m: int = 1                # ghost steps per scheduled point
    k: int = 1                # ghost steps only every k-th real iteration
    lag: int = 0              # ghost skips its first `lag` opportunities  (ghost lags)
    peel: int = 0             # ghost runs `peel` steps before the real loop (ghost leads)
    exit: str = 'assert'      # assert | rest
    when: object = None       # optional Expr predicate (data-dependent alignment) evaluated per iteration
    prophecy: bool = False    # schedule may read the prophecy value  N = number of real iterations
    inner: object = None      # SeqPlan for nested placement

    def key(self):
        return (self.place, self.m, self.k, self.lag, self.peel, self.exit, repr(self.when), self.prophecy,
                self.inner.key() if self.inner else None)

    def describe(self):
        s = f'{self.place}'
        if self.m != 1:
            s += f' {self.m}-steps'
        if self.k != 1:
            s += f' every-{self.k}'
        if self.lag:
            s += f' lag{self.lag}'
        if self.peel:
            s += f' peel{self.peel}'
        if self.when is not None:
            from .dafny import ex
            s += f' when[{ex(self.when)}]'
        if self.prophecy:
            s += ' prophecy'
        s += f' exit:{self.exit}'
        if self.inner is not None:
            s += ' {' + self.inner.describe() + '}'
        return s


@dataclass
class SeqPlan:
    match: list = field(default_factory=list)   # list of (i, j) indices into top_items of A, B
    loops: dict = field(default_factory=dict)   # (i,j) -> LoopPlan or SeqPlan-pair for ifs

    def key(self):
        return (tuple(self.match), tuple(sorted((k, v.key() if hasattr(v, 'key') else repr(v)) for k, v in self.loops.items())))

    def describe(self):
        if not self.match:
            return 'sequential'
        parts = []
        for (i, j) in self.match:
            p = self.loops.get((i, j))
            parts.append(f'{i}~{j}:' + (p.describe() if p is not None else '?'))
        return '; '.join(parts)


@dataclass
class IfPlan:
    th: SeqPlan
    el: SeqPlan

    def key(self):
        return ('if', self.th.key(), self.el.key())

    def describe(self):
        return f'if[{self.th.describe()} | {self.el.describe()}]'


class Weaver:
    def __init__(self, locals_):
        self.locals = locals_   # name -> (ty, ghost)
        self.n = 0
        self.loop_meta = {}     # woven loop lid -> info (for invariant mining / reporting)

    def fresh(self, base, ty, ghost=True):
        self.n += 1
        nm = f'g_{base}{self.n}'
        self.locals[nm] = (ty, ghost)
        return nm

    def guarded(self, g, ss):
        ss = mark_ghost(copy.deepcopy(ss))
        if not ss:
            return []
        if g is None:
            return ss
        return [If(g, ss, [], ghost=True)]

    def weave_seq(self, A, B, g, plan: SeqPlan):
        ia, ib = top_items(A), top_items(B)
        out = []
        pa = pb = 0
        for (i, j) in plan.match:
            ka, kb = ia[i], ib[j]
            out += A[pa:ka]
            out += self.guarded(g, B[pb:kb])
            sub = plan.loops.get((i, j))
            sa, sb = A[ka], B[kb]
            if isinstance(sa, While) and isinstance(sb, While):
                out += self.weave_loop(sa, sb, g, sub or LoopPlan())
            elif isinstance(sa, If) and isinstance(sb, If):
                out += self.weave_if(sa, sb, g, sub or IfPlan(SeqPlan(), SeqPlan()))
            else:
                out += [sa] + self.guarded(g, [sb])
            pa, pb = ka + 1, kb + 1
        out += A[pa:]
        out += self.guarded(g, B[pb:])
        return out

    def weave_if(self, sa: If, sb: If, g, plan: IfPlan):
        snap = self.fresh('c', BOOL)
        gt = mk_and(g, Var(snap, BOOL)) if g is not None else Var(snap, BOOL)
        gf = mk_and(g, mk_not(Var(snap, BOOL))) if g is not None else mk_not(Var(snap, BOOL))
        pre = [Assign(snap, sb.c, ghost=True)]
        th = self.weave_seq(sa.th, sb.th, gt, plan.th) + self.guarded(gf, sb.el)
        el = self.weave_seq(sa.el, sb.el, gf, plan.el) + self.guarded(gt, sb.th)
        return pre + [If(sa.c, th, el, ghost=False)]

    def step(self, M: While, g):
        """one guarded ghost step of loop M"""
        c = mk_and(g, M.c) if g is not None else M.c
        return [If(c, mark_ghost(copy.deepcopy(M.body)), [], ghost=True)]

    def weave_loop(self, L: While, M: While, g, p: LoopPlan):
        out = []
        for _ in range(p.peel):
            out += self.step(M, g)
        cnt = None
        need_cnt = p.k > 1 or p.lag > 0 or p.prophecy
        if need_cnt:
            cnt = self.fresh('it', INT)
            out.append(Assign(cnt, Const(0, INT), ghost=True))
        sched = TRUE
        if p.k > 1:
            sched = mk_and(sched, Bin('==', Bin('%', Var(cnt, INT), Const(p.k, INT), INT), Const(p.k - 1, INT), BOOL))
        if p.lag > 0:
            sched = mk_and(sched, Bin('>=', Var(cnt, INT), Const(p.lag, INT), BOOL))
        snap_when = None
        pre_body = []
        if p.when is not None:
            snap_when = self.fresh('w', BOOL)
            pre_body.append(Assign(snap_when, p.when, ghost=True))
            sched = mk_and(sched, Var(snap_when, BOOL))
        gg = mk_and(g, sched) if g is not None else (None if isinstance(sched, Const) else sched)
        if p.place == 'nested' and p.inner is not None:
            snap = self.fresh('go', BOOL)
            cond = mk_and(gg, M.c) if gg is not None else M.c
            body = pre_body + [Assign(snap, cond, ghost=True)] + \
                self.weave_seq(L.body, M.body, Var(snap, BOOL), p.inner)
        else:
            ghost_steps = []
            for _ in range(p.m):
                ghost_steps += self.step(M, gg)
            if p.place == 'begin':
                body = pre_body + ghost_steps + list(L.body)
            else:
                body = pre_body + list(L.body) + ghost_steps
        if cnt is not None:
            body = body + [Assign(cnt, Bin('+', Var(cnt, INT), Const(1, INT), INT), ghost=True)]
        wl = While(L.c, body, L.lid, [], None, False, label=L.lid)
        self.loop_meta[L.lid] = {'real': L.lid, 'ghost': M.lid, 'plan': p, 'cnt': cnt}
        out.append(wl)
        fin = mk_and(g, M.c) if g is not None else M.c
        if p.exit == 'assert':
            out.append(Assert(mk_not(fin), tag='ghost-exit:' + M.lid, ghost=True))
        else:
            rest = mark_ghost(copy.deepcopy(M))
            rest.c = fin
            rest.lid = M.lid + 'r'
            rest.label = rest.lid
            out.append(rest)
        return out


# ------------------------------------------------------------------ candidate enumeration
def monotone_matchings(na, nb, maxn=6):
    """All order-preserving partial matchings, largest first (a few)."""
    res = []
    for r in range(min(na, nb), -1, -1):
        for ia in itertools.combinations(range(na), r):
            for ib in itertools.combinations(range(nb), r):
                res.append(list(zip(ia, ib)))
                if len(res) >= maxn:
                    return res
    return res


def loop_plan_space(L: While, M: While, ratio_hint=None, preds=()):
    """Ordered candidate plans for one matched loop pair.  ratio_hint from traces: dict with
    keys 'm','k','peel','lag','exit'."""
    cands = []
    nested = has_loop(L.body) and has_loop(M.body)
    places = ['end', 'begin'] + (['nested'] if nested else [])
    hint = ratio_hint or {}
    m = hint.get('m', 1)
    k = hint.get('k', 1)
    peel = hint.get('peel', 0)
    lag = hint.get('lag', 0)
    exit_ = hint.get('exit', 'assert')
    base = []
    for place in places:
        base.append(LoopPlan(place=place, m=m, k=k, peel=peel, lag=lag, exit=exit_))
    # alternatives around the hint
    for place in places:
        for (mm, kk, pe, la, exm) in [(1, 1, 0, 0, 'assert'), (1, 1, 0, 0, 'rest'), (1, 1, 1, 0, 'assert'),
                                      (1, 1, 0, 1, 'assert'), (2, 1, 0, 0, 'assert'), (1, 2, 0, 0, 'assert'),
                                      (1, 1, 1, 0, 'rest'), (1, 1, 0, 1, 'rest')]:
            base.append(LoopPlan(place=place, m=mm, k=kk, peel=pe, lag=la, exit=exm))
    for pr in preds:
        for exm in ('assert', 'rest'):
            base.append(LoopPlan(place='end', when=pr, exit=exm))
    seen = set()
    for c in base:
        if c.key() in seen:
            continue
        seen.add(c.key())
        cands.append(c)
    return cands
