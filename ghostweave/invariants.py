"""Loop invariants for woven programs: mine candidates from concrete runs of the woven program, then
prune them with Houdini, using Dafny as the oracle.  No user-written invariants."""
from __future__ import annotations
import copy
import math
import random
from fractions import Fraction
from math import gcd
from functools import reduce
from .ir import *
from .interp import Interp, Diverge, Undefined
from . import dafny as D


def all_loops(ss, acc=None):
    if acc is None:
        acc = []
    for s in ss:
        if isinstance(s, While):
            acc.append(s)
            all_loops(s.body, acc)
        elif isinstance(s, If):
            all_loops(s.th, acc); all_loops(s.el, acc)
    return acc


def relabel(body):
    for n, w in enumerate(all_loops(body)):
        w.label = f'W{n}'
        w.lid = w.label


# ------------------------------------------------------------------ concrete runs
def run_woven(body, locals_, inputs_list, fuel=20000, externs=None):
    """Run woven body on each input env; returns (samples by label, n_ok, failures)."""
    samples = {}
    ok = 0
    fails = []

    def probe(label, env):
        lst = samples.setdefault(label, [])
        if len(lst) < 400:
            lst.append(dict(env))

    for inp in inputs_list:
        env = dict(inp)
        it = Interp(fuel, externs=externs, probe=probe)
        try:
            it.run(body, env)
            ok += 1
        except AssertionError as e:
            fails.append(('assert', str(e), inp))
        except (Diverge, Undefined, RecursionError, OverflowError, ZeroDivisionError, TypeError):
            pass
    return samples, ok, fails


# ------------------------------------------------------------------ affine equalities (exact)
def nullspace(rows, ncols):
    """rows: list of lists of Fractions (each sample); returns basis of {c | rows . c = 0}."""
    m = [list(r) for r in rows]
    piv_cols = []
    r = 0
    for c in range(ncols):
        p = None
        for i in range(r, len(m)):
            if m[i][c] != 0:
                p = i
                break
        if p is None:
            continue
        m[r], m[p] = m[p], m[r]
        pv = m[r][c]
        m[r] = [x / pv for x in m[r]]
        for i in range(len(m)):
            if i != r and m[i][c] != 0:
                f = m[i][c]
                m[i] = [a - f * b for a, b in zip(m[i], m[r])]
        piv_cols.append(c)
        r += 1
        if r == len(m):
            break
    free = [c for c in range(ncols) if c not in piv_cols]
    basis = []
    for fc in free:
        v = [Fraction(0)] * ncols
        v[fc] = Fraction(1)
        for i, pc in enumerate(piv_cols):
            v[pc] = -m[i][fc]
        basis.append(v)
    return basis


def lin_expr(coeffs, names, const, ty=INT):
    """sum coeffs[i]*names[i] == const as IR expr, with integer coefficients."""
    terms = None
    for c, n in zip(coeffs, names):
        if c == 0:
            continue
        if isinstance(n, tuple):
            v = Var(n[0], ty) if len(n) == 1 else Bin('*', Var(n[0], ty), Var(n[1], ty), ty)
        else:
            v = Var(n, ty)
        k = Const(c, INT) if ty == INT else Const(float(c), REAL)
        t = v if c == 1 else (Un('neg', v, ty) if c == -1 else Bin('*', k, v, ty))
        terms = t if terms is None else Bin('+', terms, t, ty)
    if terms is None:
        return None
    return Bin('==', terms, Const(const, INT) if ty == INT else Const(float(const), REAL), BOOL)


def affine_invariants(samples, names, max_vars=24, ty=INT, products=()):
    """Exact affine equalities over `names` (and optional product features (u, v) meaning u*v)."""
    if not names or not samples:
        return []
    names = names[:max_vars]
    products = list(products)[:16]
    feats = [(n,) for n in names] + [tuple(p) for p in products]
    rows = []
    seen = set()

    def val(s, f):
        v = s[f[0]] if len(f) == 1 else s[f[0]] * s[f[1]]
        return Fraction(v) if isinstance(v, float) else Fraction(int(v))
    for s in samples:
        key = tuple(s[n] for n in names)
        if key in seen:
            continue
        seen.add(key)
        rows.append([val(s, f) for f in feats] + [Fraction(1)])
    if len(rows) < 2:
        return []
    basis = nullspace(rows, len(feats) + 1)
    out = []
    for v in basis:
        den = reduce(lambda a, b: a * b // gcd(a, b), [x.denominator for x in v], 1)
        iv = [int(x * den) for x in v]
        g = reduce(gcd, [abs(x) for x in iv if x != 0], 0) or 1
        iv = [x // g for x in iv]
        # normalise sign: first nonzero coefficient positive
        for x in iv[:-1]:
            if x != 0:
                if x < 0:
                    iv = [-y for y in iv]
                break
        if sum(1 for x in iv[:-1] if x != 0) > 4:
            continue  # too dense, unlikely to be meaningful
        if ty == REAL and max(abs(x) for x in iv) > 10 ** 6:
            continue
        e = lin_expr(iv[:-1], feats, -iv[-1], ty)
        if e is not None:
            out.append(e)
    return out


# ------------------------------------------------------------------ candidate generation
def side(n):
    if n.startswith('l_'):
        return 'l'
    if n.startswith('r_'):
        return 'r'
    return 'g'


def mine(samples, types, guard_vars=frozenset(), extra=(), changed=None):
    """types: name -> type for variables that may appear in invariants at this loop head."""
    if not samples:
        return list(extra)
    cand = []
    names = [n for n in types if all(n in s and s[n] is not None for s in samples)]
    ints = sorted(n for n in names if types[n] == INT and all(isinstance(s[n], int) and not isinstance(s[n], bool) for s in samples))
    reals = sorted(n for n in names if types[n] == REAL)
    bools = sorted(n for n in names if types[n] == BOOL)
    seqs = sorted(n for n in names if is_seq(types[n]))

    def holds(f):
        try:
            return all(f(s) for s in samples)
        except Exception:
            return False

    # equalities between same-typed variables
    for grp, ty in ((ints, INT), (reals, REAL), (bools, BOOL), (seqs, None)):
        for i, a in enumerate(grp):
            for b in grp[i + 1:]:
                if ty is None and types[a] != types[b]:
                    continue
                if holds(lambda s: s[a] == s[b]):
                    cand.append(Bin('==', Var(a, types[a]), Var(b, types[b]), BOOL))
    # constants for reals / bools
    for a in reals:
        v = samples[0][a]
        if holds(lambda s: s[a] == v) and isinstance(v, float) and abs(v) < 1e12 and v == float(Fraction(v).limit_denominator(1000)):
            cand.append(Bin('==', Var(a, REAL), Const(v, REAL), BOOL))
    for a in bools:
        v = samples[0][a]
        if holds(lambda s: s[a] == v):
            cand.append(Var(a, BOOL) if v else mk_not(Var(a, BOOL)))
    # boolean implications between ghost/real flags
    for a in bools:
        for b in bools:
            if a != b and holds(lambda s: (not s[a]) or s[b]):
                cand.append(Bin('==>', Var(a, BOOL), Var(b, BOOL), BOOL))
    # affine equalities over integers / reals (the core relational invariants)
    prods = []
    if changed is not None:
        frozen_ = [a for a in ints if a not in changed and len({s[a] for s in samples}) > 1]
        moving = [a for a in ints if a in changed]
        prods = [(u, v) for u in frozen_ for v in moving]
    cand += affine_invariants(samples, ints)
    if prods:
        cand += [e for e in affine_invariants(samples, ints, products=prods)
                 if any(isinstance(t, Bin) and t.op == '*' for t in _terms(e))]
    finite_reals = [a for a in reals if holds(lambda s: isinstance(s[a], float) and math.isfinite(s[a]) and abs(s[a]) < 1e9)]
    cand += affine_invariants(samples, finite_reals, ty=REAL)
    # inequalities: cross-side pairs and guard-variable pairs
    for i, a in enumerate(ints):
        for b in ints[i + 1:]:
            if side(a) == side(b) and a not in guard_vars and b not in guard_vars:
                continue
            for op, f in (('<=', lambda x, y: x <= y), ('>=', lambda x, y: x >= y)):
                if holds(lambda s: f(s[a], s[b])):
                    cand.append(Bin(op, Var(a, INT), Var(b, INT), BOOL))
    for a in ints:
        for c in (0, 1):
            if holds(lambda s: s[a] >= c):
                cand.append(Bin('>=', Var(a, INT), Const(c, INT), BOOL))
    # sequence lengths
    for a in seqs:
        for b in seqs:
            if a < b and types[a] == types[b] and holds(lambda s: len(s[a]) == len(s[b])):
                cand.append(Bin('==', Len(Var(a, types[a])), Len(Var(b, types[b])), BOOL))
        for b in ints:
            if holds(lambda s: len(s[a]) == s[b]):
                cand.append(Bin('==', Len(Var(a, types[a])), Var(b, INT), BOOL))
    for e in extra:
        cand.append(e)
    # dedupe
    out, seen = [], set()
    for e in cand:
        k = D.ex(e)
        if k not in seen:
            seen.add(k)
            out.append(e)
    return out


def mine_conditional(samples, types, antecedents, guard_vars=frozenset()):
    """Disjunctive invariants of the form  p ==> c, mined on the samples where p holds.
    Antecedents are loop guards and ghost-schedule facts (e.g. g_it >= 1 for a lagging ghost)."""
    out = []
    ev = Interp()
    for p in antecedents:
        sub = []
        for s_ in samples:
            try:
                if ev.ev(p, s_):
                    sub.append(s_)
            except Exception:
                sub = None
                break
        if not sub or len(sub) == len(samples) or len(sub) < 2:
            continue
        base = {D.ex(e) for e in mine(samples, types, guard_vars)}
        for c in mine(sub, types, guard_vars):
            if D.ex(c) not in base:
                out.append(Bin('==>', p, c, BOOL))
    return out


def antecedents_for(loop, body):
    """Candidate antecedents at the head of `loop`: guards of loops and ghost counters."""
    ants = []
    for w in all_loops(body):
        ants.append(w.c)
    names = assigned_vars(loop.body)
    for n in sorted(names):
        if n.startswith('g_it'):
            ants.append(Bin('>=', Var(n, INT), Const(1, INT), BOOL))
    ants = ants[:6]
    ants = ants + [mk_not(a) for a in ants]
    out, seen = [], set()
    for a in ants:
        k = D.ex(a)
        if k not in seen:
            seen.add(k)
            out.append(a)
    return out


def _terms(e):
    out = []
    def go(x):
        if isinstance(x, Bin) and x.op in ('+', '=='):
            go(x.l); go(x.r)
        else:
            out.append(x)
    go(e)
    out2 = []
    for t in out:
        if isinstance(t, Bin) and t.op == '*' and isinstance(t.l, Var) and isinstance(t.r, Var):
            out2.append(t)
        elif isinstance(t, Bin) and t.op == '*' and isinstance(t.r, Bin):
            out2.append(t.r)
        elif isinstance(t, Un) and isinstance(t.e, Bin):
            out2.append(t.e)
    return out2


def guard_vars_of(body):
    acc = set()
    for w in all_loops(body):
        expr_vars(w.c, acc)
    return acc


def score_candidates(cands, changed=None):
    """number of cross-side relational facts between variables the loop actually changes: an
    alignment is good when the woven loop heads satisfy many relations between the evolving
    states of P1 and P2 (relations with frozen variables are what self-composition gives you)."""
    sc = 0
    for e in cands:
        vs = expr_vars(e)
        if changed is not None:
            vs = vs & changed
        sides = {side(v) for v in vs}
        if 'l' in sides and 'r' in sides:
            sc += 1
    return sc


# ------------------------------------------------------------------ Houdini over Dafny
def houdini(woven, externs, cand_by_label, max_rounds=14, timeout=180, vc_limit=60, log=None, keep=None):
    """woven: method dict (see dafny.emit_method) whose body loops carry labels.
    Iteratively drops invariants Dafny reports as failing.  Returns (DafnyResult, final text, rounds)."""
    cur = {k: list(v) for k, v in cand_by_label.items()}
    res = None
    text = ''
    for rnd in range(max_rounds):
        w = copy.deepcopy(woven)
        for lp in all_loops(w['body']):
            lp.invs = list(cur.get(lp.label, []))
        text, em = D.emit_method(w, externs)
        res = D.run_dafny(text, timeout=timeout, vc_limit=vc_limit, keep=keep)
        if log is not None:
            log.append((rnd, len(res.errors), [m for _, m in res.errors][:6], res.timeout))
        if res.ok:
            return res, text, rnd + 1
        bad = {}
        for line, msg in res.errors:
            if line in em.inv_lines:
                lid, k = em.inv_lines[line]
                bad.setdefault(lid, set()).add(k)
        if not bad:
            if res.timeout and rnd == 0:
                # whole-file timeout: try once more with fewer candidates (drop inequalities)
                cur = {k: [e for e in v if not (isinstance(e, Bin) and e.op in ('<=', '>='))] for k, v in cur.items()}
                continue
            return res, text, rnd + 1
        for lid, ks in bad.items():
            cur[lid] = [e for i, e in enumerate(cur[lid]) if i not in ks]
    return res, text, max_rounds
