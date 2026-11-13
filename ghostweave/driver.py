"""End-to-end: (P1, P2) -> differential testing -> alignment search -> invariant inference -> Dafny."""
from __future__ import annotations
import copy
import dataclasses
import math
import random
import time
from .ir import *
from .interp import Interp, Diverge, Undefined, run_func, rec_impls
from .weave import (Weaver, SeqPlan, LoopPlan, IfPlan, top_items, label_loops, mark_ghost, has_loop,
                    monotone_matchings, loop_plan_space, if_conditions)
from .invariants import (run_woven, mine, score_candidates, houdini, relabel, all_loops, guard_vars_of,
                         mine_conditional, antecedents_for)
from . import dafny as D


# ------------------------------------------------------------------ inputs
def rand_val(ty, rng, n_hint=None):
    if ty == INT:
        r = rng.random()
        if r < 0.6:
            return rng.randint(-6, 12)
        if r < 0.9:
            return rng.randint(-60, 100)
        return rng.randint(-2000, 2000)
    if ty == REAL:
        r = rng.random()
        if r < 0.3:
            return float(rng.randint(-5, 10))
        if r < 0.85:
            return rng.randint(-80, 160) / 8.0      # dyadic: arithmetic stays exact
        return rng.uniform(-200, 200)
    if ty == BOOL:
        return rng.random() < 0.5
    if is_seq(ty):
        n = rng.randint(0, 9) if n_hint is None else n_hint
        return tuple(rand_val(ty[1], rng) for _ in range(n))
    raise ValueError(ty)


def gen_inputs(params, n, seed=0):
    rng = random.Random(seed)
    out = []
    for _ in range(n):
        alen = rng.randint(1, 10)
        d = {}
        for name, ty in params:
            d[name] = rand_val(ty, rng, alen if is_seq(ty) else None)
        out.append(d)
    return out


def values_equal(a, b):
    if isinstance(a, float) or isinstance(b, float):
        if a is None or b is None:
            return a is b
        return math.isclose(a, b, rel_tol=1e-9, abs_tol=1e-12)
    if isinstance(a, tuple) and isinstance(b, tuple):
        return len(a) == len(b) and all(values_equal(x, y) for x, y in zip(a, b))
    return a == b


def differential_test(p1, p2, n=400, seed=1):
    ps1 = p1.func.params
    ps2 = p2.func.params
    if [t for _, t in ps1] != [t for _, t in ps2]:
        return None
    e1, e2 = rec_impls(p1), rec_impls(p2)
    for inp in gen_inputs(ps1, n, seed):
        inp2 = {n2: inp[n1] for (n1, _), (n2, _) in zip(ps1, ps2)}
        try:
            o1 = run_func(p1.func, inp, externs=e1)
            o2 = run_func(p2.func, inp2, externs=e2)
        except (Diverge, Undefined, RecursionError, OverflowError, ZeroDivisionError, TypeError, AssertionError):
            continue
        if not values_equal(o1, o2):
            return {'input': inp, 'out1': o1, 'out2': o2}
    return None


# ------------------------------------------------------------------ problem set-up
class Problem:
    """Relational verification problem: P1 real, P2 ghost, pre/post over in_/out_ names."""

    def __init__(self, p1, p2, pre=None, post_obs=None, shared=(), post_raw=None):
        """shared: recursive functions f whose P1/P2 versions are identified (one UF rec_f) because a
        mutual-summary obligation was discharged (or is being discharged, inductively)."""
        self.p1, self.p2 = p1, p2
        f1, f2 = p1.func, p2.func
        self.locals = {}
        for n, t in f1.locals.items():
            self.locals['l_' + n] = (t, False)
        for n, t in f2.locals.items():
            self.locals['r_' + n] = (t, True)
        rl = {'rec_' + f: 'rec_' + f + '__l' for f in getattr(p1, 'rec_funcs', {})}
        rr = {'rec_' + f: 'rec_' + f + '__r' for f in getattr(p2, 'rec_funcs', {})}
        self.A = rename_calls(rename_stmts(f1.body, lambda n: 'l_' + n), rl)
        self.B = mark_ghost(rename_calls(rename_stmts(f2.body, lambda n: 'r_' + n), rr))
        self.call_alias = {}
        for f in shared:
            self.call_alias['rec_' + f + '__l'] = 'rec_' + f
            self.call_alias['rec_' + f + '__r'] = 'rec_' + f
        self.interp_externs = dict(rec_impls(p1, '__l'))
        self.interp_externs.update(rec_impls(p2, '__r'))
        label_loops(self.A, 'L', [0])
        label_loops(self.B, 'R', [0])
        self.params = [('in_l_' + n, t, False) for n, t in f1.params] + [('in_r_' + n, t, True) for n, t in f2.params]
        self.prefix = [Assign('l_' + n, Var('in_l_' + n, t)) for n, t in f1.params] + \
                      [Assign('r_' + n, Var('in_r_' + n, t), ghost=True) for n, t in f2.params]
        if pre is None:
            pre = [Bin('==', Var('in_l_' + a, t), Var('in_r_' + b, t), BOOL)
                   for (a, t), (b, _) in zip(f1.params, f2.params)]
        self.pre = pre
        # observables
        if post_obs is None:
            post_obs = []
            if f1.ret_ty is not None:
                post_obs.append(('ret', 'ret', f1.ret_ty))
            for a, b in zip(f1.out_params, f2.out_params):
                post_obs.append((a, b, f1.locals[a]))
        self.obs = post_obs
        self.outs = []
        self.suffix = []
        self.post = []
        for k, (a, b, t) in enumerate(post_obs):
            self.outs += [(f'out_l_{k}', t, False), (f'out_r_{k}', t, True)]
            self.suffix += [Assign(f'out_l_{k}', Var('l_' + a, t)), Assign(f'out_r_{k}', Var('r_' + b, t), ghost=True)]
            self.post.append(Bin('==', Var(f'out_l_{k}', t), Var(f'out_r_{k}', t), BOOL))
        if post_raw is not None:
            # relational postcondition over the final states (KestRel style): checked as a final assertion
            self.suffix.append(Assert(post_raw, tag='post', ghost=True))
        self.externs = {rl.get(k, k): v for k, v in p1.externs.items()}
        self.externs.update({rr.get(k, k): v for k, v in p2.externs.items()})

    def weave(self, plan):
        locs = dict(self.locals)
        w = Weaver(locs)
        body = w.weave_seq(copy.deepcopy(self.A), copy.deepcopy(self.B), None, plan)
        body = copy.deepcopy(self.prefix) + body + copy.deepcopy(self.suffix)
        relabel(body)
        return {'params': self.params, 'outs': self.outs, 'requires': self.pre, 'ensures': self.post,
                'locals': locs, 'body': body, 'call_alias': self.call_alias}

    def woven_inputs(self, n, seed=3):
        """inputs satisfying the relational precondition (equal inputs by default)."""
        f1, f2 = self.p1.func, self.p2.func
        out = []
        tries = 0
        rng = random.Random(seed)
        while len(out) < n and tries < n * 20:
            tries += 1
            base = gen_inputs(f1.params, 1, seed=rng.randint(0, 10 ** 9))[0]
            d = {}
            for (a, t), (b, _) in zip(f1.params, f2.params):
                d['in_l_' + a] = base[a]
                d['in_r_' + b] = base[a]
            if self.custom_pre_sampler:
                d = self.custom_pre_sampler(d, rng)
                if d is None:
                    continue
            try:
                if not all(Interp().ev(p, d) for p in self.pre):
                    continue
            except Exception:
                continue
            out.append(d)
        return out

    custom_pre_sampler = None


# ------------------------------------------------------------------ plan enumeration
def pair_options(sa, sb, depth):
    if isinstance(sa, While) and isinstance(sb, While):
        preds = []
        if depth == 0:
            preds = [c for c in if_conditions(sa.body) if not has_loop([])][:3]
        base = loop_plan_space(sa, sb, preds=preds)
        if depth > 0:
            base = base[:6]
        res = []
        for lp in base:
            if lp.place == 'nested':
                for inner in seq_plans(sa.body, sb.body, depth + 1, limit=3):
                    res.append(dataclasses.replace(lp, inner=inner))
            else:
                res.append(lp)
        return res
    if isinstance(sa, If) and isinstance(sb, If):
        ths = seq_plans(sa.th, sb.th, depth + 1, 3)
        els = seq_plans(sa.el, sb.el, depth + 1, 3)
        return [IfPlan(t, e) for t in ths for e in els][:6]
    return [None]


def seq_plans(A, B, depth=0, limit=80):
    ia, ib = top_items(A), top_items(B)
    if not ia or not ib:
        return [SeqPlan()]
    out = []
    for M in monotone_matchings(len(ia), len(ib), maxn=3 if depth else 5):
        if not M:
            out.append(SeqPlan())
            continue
        options = [pair_options(A[ia[i]], B[ib[j]], depth) for (i, j) in M]
        default = [o[0] for o in options]
        out.append(SeqPlan(M, dict(zip(M, default))))
        for idx, opts in enumerate(options):
            for o in opts[1:]:
                ch = list(default)
                ch[idx] = o
                out.append(SeqPlan(M, dict(zip(M, ch))))
    return out[:limit]


def plan_complexity(plan):
    s = plan.describe()
    return len(s)


# ------------------------------------------------------------------ main entry
def verify(prob: Problem, n_inputs=40, top_k=5, time_budget=600, log=None, keep_dir=None, verbose=False):
    t0 = time.time()
    info = {'plans_total': 0, 'plans_viable': 0, 'tried': []}
    inputs = prob.woven_inputs(n_inputs)
    info['n_inputs'] = len(inputs)
    plans = seq_plans(prob.A, prob.B)
    info['plans_total'] = len(plans)
    scored = []
    types_all = {n: t for n, (t, g) in prob.locals.items()}
    for idx, plan in enumerate(plans):
        try:
            woven = prob.weave(plan)
        except Exception as ex:  # pragma: no cover
            continue
        types = {n: t for n, (t, g) in woven['locals'].items()}
        samples, ok, fails = run_woven(woven['body'], woven['locals'], inputs, externs=prob.interp_externs)
        if fails:
            continue  # the ghost program counter did not reach the end on some run: reject
        gv = guard_vars_of(woven['body'])
        cands = {}
        sc = 0
        for lp in all_loops(woven['body']):
            smp = samples.get(lp.label, [])
            cs = mine(smp, types, gv, changed=assigned_vars(lp.body))
            sc += score_candidates(cs, assigned_vars(lp.body))
            cands[lp.label] = cs
            cands.setdefault('__cond__', {})[lp.label] = mine_conditional(smp, types, antecedents_for(lp, woven['body']), gv)
        scored.append((-sc, idx, plan, woven, cands, ok))
    info['plans_viable'] = len(scored)
    scored.sort(key=lambda x: (x[0], x[1]))
    if not scored:
        return 'unknown', info
    for (negsc, idx, plan, woven, cands, ok) in scored[:top_k]:
        if time.time() - t0 > time_budget:
            info['budget_exhausted'] = True
            break
        hl = []
        cond = cands.pop('__cond__', {})
        res, text, rounds = houdini(woven, prob.externs, cands, log=hl)
        if not res.ok and any(cond.values()) and time.time() - t0 < time_budget:
            # stage 2: add disjunctive (implication) candidates
            c2 = {k: v + cond.get(k, []) for k, v in cands.items()}
            res, text, r2 = houdini(woven, prob.externs, c2, log=hl)
            rounds += r2
        info['tried'].append({'plan': plan.describe(), 'score': -negsc, 'rounds': rounds, 'ok': res.ok,
                              'errors': [m for _, m in res.errors][:3], 'timeout': res.timeout})
        if verbose:
            print('  plan', plan.describe(), 'score', -negsc, '->', res.ok, [m for _, m in res.errors][:2])
        if res.ok:
            info['plan'] = plan.describe()
            info['dafny'] = text
            info['time'] = time.time() - t0
            return 'proved', info
    info['time'] = time.time() - t0
    return 'unknown', info


def prove_recursive(p1, p2, **kw):
    """Mutual summaries (Godlin & Strichman): assume every common recursive function f is equivalent
    in P1 and P2 (calls replaced by one UF), check each body pair under that assumption, drop the
    ones that fail and repeat (greatest fixpoint).  Sound for partial equivalence."""
    r1, r2 = getattr(p1, 'rec_funcs', {}), getattr(p2, 'rec_funcs', {})
    cand = set()
    for f in set(r1) & set(r2):
        a, b = r1[f].func, r2[f].func
        if [t for _, t in a.params] == [t for _, t in b.params] and a.ret_ty == b.ret_ty and not a.out_params:
            cand.add(f)
    details = {}
    while True:
        failed = set()
        for f in sorted(cand):
            sub = Problem(r1[f], r2[f], shared=cand)
            verdict, info = verify(sub, **kw)
            details[f] = verdict
            if verdict != 'proved':
                failed.add(f)
        if not failed:
            return cand, details
        cand -= failed
