"""Forall-exists (refinement / GNI) verification by ghost weaving.

    for every run of PA (forall side, real code) there is a run of PE (exists side, ghost code)
    such that post holds.

PA's nondeterministic choices are real havocs constrained by their aspec.  PE's choices become ghost
assignments  x := W  of a *witness term* W followed by the ghost obligation espec_pre(W); PE's
`assume(c)` becomes a ghost `assert c` (the chosen run must not be blocked); ghost loops must
terminate (Dafny checks it), so the exists-run really is a complete run.

Witness terms come from a small grammar: the forall side's most recent choice of the same function
("copy the adversary"), constants from the specs, state variables, `c - v`, and *prophecy* values.
A prophecy witness is a ghost input p resolved at the end of the program by  p == l_v  for a final
forall-side variable l_v.  The obligations are accumulated into a ghost flag `ok` and the method
checks  (p == l_v) ==> ok.  This is sound: the real run does not depend on p, so for each real run
take p := its final l_v.
"""
from __future__ import annotations
import copy
import itertools
import os
import random
import re
import time
from .ir import *
from .interp import Interp, Diverge, Undefined
from .invariants import (run_woven, mine, score_candidates, houdini, relabel, all_loops, guard_vars_of,
                         mine_conditional, antecedents_for)
from .driver import Problem, seq_plans
from . import dafny as D


def cond_to_py(text):
    t = text.replace('ret!', '__ret')
    t = t.replace('&&', ' and ').replace('||', ' or ')
    t = re.sub(r'!(?!=)', ' not ', t)
    t = re.sub(r'\btrue\b', 'True', t)
    t = re.sub(r'\bfalse\b', 'False', t)
    if '==>' in t or 'forall' in t or 'exists' in t:
        return None
    return t


def py_pred(text):
    """python predicate over an environment for a C/Dafny condition (None-safe: unknown -> True)"""
    t = cond_to_py(text)
    if t is None:
        return None
    try:
        code = compile(t, '<cond>', 'eval')
    except SyntaxError:
        return None

    def f(env):
        try:
            return bool(eval(code, {}, dict(env)))
        except Exception:
            return True
    return f


def subst_text(text, mapping):
    """replace whole-word identifiers by (parenthesised) texts"""
    if not mapping:
        return text
    pat = re.compile(r'(?<![\w.])(' + '|'.join(re.escape(k) for k in sorted(mapping, key=len, reverse=True)) + r')\b')
    return pat.sub(lambda m: '(' + mapping[m.group(1)] + ')', text)


class Spec:
    def __init__(self, params, choice_vars, pre, post):
        self.params, self.choice_vars, self.pre, self.post = params, choice_vars, pre, post


def parse_specs(block):
    """'f(a, b) { choiceVars: n; pre: ...; post: ...; }' entries"""
    out = {}
    for m in re.finditer(r'(\w+)\s*\(([^)]*)\)\s*\{(.*?)\}', block, re.S):
        name, params, body = m.group(1), [p.strip() for p in m.group(2).split(',') if p.strip()], m.group(3)
        def fld(k):
            mm = re.search(k + r'\s*:(.*?);', body, re.S)
            return ' '.join(mm.group(1).split()) if mm else None
        cv = fld('choiceVars')
        out[name] = Spec(params, [c.strip() for c in cv.split(',')] if cv else [], fld('pre') or 'true', fld('post') or 'true')
    return out


def ints_in(text):
    return sorted({int(x) for x in re.findall(r'(?<![\w.])-?\d+(?![\w.])', text or '')})


class AEProblem(Problem):
    def __init__(self, pA, pE, pre_text, post_text, aspecs, especs):
        super().__init__(pA, pE, pre=[Raw(pre_text)], post_obs=[], post_raw=Raw(post_text, py=py_pred(post_text)))
        self.aspecs, self.especs = aspecs, especs
        self.post_text = post_text
        # exists-side assumes are obligations
        def conv(ss):
            out = []
            for s in ss:
                if isinstance(s, Assume):
                    out.append(Assert(s.e, tag='exists-assume', ghost=True))
                elif isinstance(s, If):
                    out.append(If(s.c, conv(s.th), conv(s.el), s.ghost))
                elif isinstance(s, While):
                    w = copy.copy(s)
                    w.body = conv(s.body)
                    out.append(w)
                else:
                    out.append(s)
            return out
        self.B = conv(self.B)
        n = [0]

        def sites(ss):
            for s in ss:
                if isinstance(s, Choose):
                    s.site = f'c{n[0]}'
                    n[0] += 1
                elif isinstance(s, If):
                    sites(s.th); sites(s.el)
                elif isinstance(s, While):
                    sites(s.body)
        sites(self.B)
        self.n_sites = n[0]
        # uninterpreted functions mentioned only in specifications still need declarations
        from .cfront import c_type
        for prog in (pA, pE):
            fe = getattr(prog, 'frontend', None)
            for name, proto in (getattr(fe, 'protos', {}) or {}).items():
                if name in aspecs or name in especs or name in self.externs:
                    continue
                try:
                    rty = c_type(proto.type.type)
                    ptys = [c_type(q.type) for q in (proto.type.args.params if proto.type.args else [])]
                    if rty is not None and None not in ptys:
                        self.externs[name] = (ptys, rty)
                except Exception:
                    pass
        self.consts = sorted(set([0, 1] + ints_in(post_text) + ints_in(pre_text) +
                                 [c for sp in especs.values() for c in ints_in(sp.pre)]))[:8]

    # --------------------------------------------------------------- dafny pieces
    def choice_specs(self):
        """real (forall-side) choices:  x :| aspec_post[ret! := x]"""
        out = {}
        for f, sp in self.aspecs.items():
            def mk(sp):
                return lambda name, args: subst_text(sp.post.replace('ret!', '__RET'), dict(zip(sp.params, args), __RET=name))
            out[f] = mk(sp)
        return out

    def espec_obligation(self, fn, wtext, argtexts, wpy):
        sp = self.especs.get(fn)
        if sp is None:
            return None
        mp = dict(zip(sp.params, argtexts))
        if sp.choice_vars:
            mp[sp.choice_vars[0]] = wtext
        text = subst_text(sp.pre, mp)
        pyt = cond_to_py(sp.pre)
        pyf = None
        if pyt is not None:
            code = compile(pyt, '<espec>', 'eval')
            def pyf(env, code=code, sp=sp, wpy=wpy, args=argtexts):
                b = {}
                if sp.choice_vars:
                    b[sp.choice_vars[0]] = wpy(env)
                for p_, a in zip(sp.params, self._argvals.get(id(env), [])):
                    b[p_] = a
                return bool(eval(code, {}, b))
        return Raw(text, py=pyf)

    # --------------------------------------------------------------- witnesses
    def witness_space(self, woven_body, locals_):
        """per site: list of (kind, payload)."""
        ints = sorted(n for n, (t, g) in locals_.items() if t == INT and (n.startswith('l_') or n.startswith('r_')))
        lfinal = [n for n in ints if n.startswith('l_')]
        space = {}
        for k in range(self.n_sites):
            c = [('copy', None)]
            c += [('const', v) for v in self.consts]
            c += [('var', v) for v in ints if v.startswith('l_')]
            c += [('diffv', (a, b)) for a in ints if a.startswith('l_') for b in ints if b.startswith('r_')]
            c += [('diff', (cst, v)) for cst in self.consts if cst != 0 for v in ints]
            c += [('var', v) for v in ints if v.startswith('r_')]
            if not os.environ.get('GW_NO_PROPHECY'):
                c += [('prophecy', v) for v in lfinal]
            space[f'c{k}'] = c
        return space

    def instantiate(self, woven, choice):
        """choice: site -> (kind, payload).  Returns a new woven dict (or None if not applicable)."""
        w = copy.deepcopy(woven)
        w['choice_specs'] = self.choice_specs()
        proph = {}
        last_real = {}
        argvals = {}
        self._argvals = argvals

        def wexpr(site, fn, ty):
            kind, pl = choice[site]
            if kind == 'copy':
                src = last_real.get(fn) or last_real.get('*')
                if src is None:
                    return None
                return Var(src, ty)
            if kind == 'const':
                return Const(pl, INT)
            if kind == 'var':
                return Var(pl, INT)
            if kind == 'diff':
                return Bin('-', Const(pl[0], INT), Var(pl[1], INT), INT)
            if kind == 'diffv':
                return Bin('-', Var(pl[0], INT), Var(pl[1], INT), INT)
            if kind == 'prophecy':
                nm = 'in_proph_' + site
                proph[site] = (nm, pl)
                return Var(nm, INT)
            return None

        bad = [False]

        def go(ss):
            out = []
            for s in ss:
                if isinstance(s, Choose) and not s.ghost:
                    last_real[s.fn] = s.name
                    last_real['*'] = s.name
                    out.append(s)
                elif isinstance(s, Choose) and s.ghost:
                    e = wexpr(s.site, s.fn, s.ty)
                    if e is None:
                        bad[0] = True
                        return out
                    if s.ty == BOOL:
                        e = Bin('!=', e, Const(0, INT), BOOL)
                    out.append(Assign(s.name, e, ghost=True))
                    ob = self.espec_obligation(s.fn, D.ex(e), [D.ex(a) for a in s.args],
                                               (lambda env, e=e: Interp().ev(e, env)))
                    if ob is not None:
                        # make arguments available to the python check
                        args = s.args
                        ob2 = Raw(ob.text, py=(None if ob.py is None else
                                                (lambda env, ob=ob, args=args: self._eval_ob(ob, args, env))))
                        out.append(Assert(ob2, tag='espec', ghost=True))
                elif isinstance(s, If):
                    out.append(If(s.c, go(s.th), go(s.el), s.ghost))
                elif isinstance(s, While):
                    s2 = copy.copy(s)
                    s2.body = go(s.body)
                    out.append(s2)
                else:
                    out.append(s)
            return out
        w['body'] = go(w['body'])
        if bad[0]:
            return None
        if proph:
            # prophecy: accumulate ghost obligations, check them under the resolution
            ok = 'g_ok'
            w['locals'][ok] = (BOOL, True)
            res = None
            for site, (nm, v) in proph.items():
                w['params'] = w['params'] + [(nm, INT, True)]
                r = Bin('==', Var(nm, INT), Var(v, INT), BOOL)
                res = r if res is None else Bin('&&', res, r, BOOL)

            def acc(ss):
                out = []
                for s in ss:
                    if isinstance(s, Assert) and s.ghost:
                        out.append(Assign(ok, Bin('&&', Var(ok, BOOL), s.e, BOOL), ghost=True))
                    elif isinstance(s, If):
                        out.append(If(s.c, acc(s.th), acc(s.el), s.ghost))
                    elif isinstance(s, While):
                        s2 = copy.copy(s)
                        s2.body = acc(s.body)
                        out.append(s2)
                    else:
                        out.append(s)
                return out
            w['body'] = [Assign(ok, TRUE, ghost=True)] + acc(w['body']) + \
                [Assert(Bin('==>', res, Var(ok, BOOL), BOOL), tag='prophecy', ghost=True)]
            w['prophecy'] = proph
        return w

    def _eval_ob(self, ob, args, env):
        vals = [Interp().ev(a, env) for a in args]
        self._argvals[id(env)] = vals
        try:
            return ob.py(env)
        finally:
            self._argvals.pop(id(env), None)


def make_chooser(aspecs, rng):
    def chooser(fn, args, env):
        sp = aspecs.get(fn)
        pyt = cond_to_py(sp.post) if sp else None
        for _ in range(200):
            v = rng.randint(-3, 25) if rng.random() < 0.9 else rng.randint(-100, 100)
            if pyt is None:
                return v
            b = dict(zip(sp.params, args))
            b['__ret'] = v
            try:
                if eval(pyt, {}, b):
                    return v
            except Exception:
                return v
        raise Undefined('no choice')
    return chooser


def run_ae(w, inputs, aspecs, fuel=20000, externs=None, stop_on_fail=True):
    """Run an instantiated woven program; prophecies are resolved by a first pass that ignores
    ghost assertions.  Returns (samples, ok_count, failures)."""
    samples, ok, fails = {}, 0, []

    def probe(label, env):
        lst = samples.setdefault(label, [])
        if len(lst) < 300:
            lst.append(dict(env))
    proph = w.get('prophecy', {})
    for k, inp in enumerate(inputs):
        env = dict(inp)
        if proph:
            env1 = dict(inp)
            for site, (nm, v) in proph.items():
                env1[nm] = 0
            it = Interp(fuel, externs=externs)
            it.chooser = make_chooser(aspecs, random.Random(k))
            try:
                _run_noassert(it, w['body'], env1)
            except (Diverge, Undefined, RecursionError, OverflowError, ZeroDivisionError, TypeError):
                continue
            for site, (nm, v) in proph.items():
                env[nm] = env1.get(v)
        it = Interp(fuel, externs=externs, probe=probe)
        it.chooser = make_chooser(aspecs, random.Random(k))
        try:
            it.run(w['body'], env)
            ok += 1
        except AssertionError as e:
            fails.append(str(e))
            if stop_on_fail:
                break
        except (Diverge, Undefined, RecursionError, OverflowError, ZeroDivisionError, TypeError):
            pass
    return samples, ok, fails


def _run_noassert(it, body, env):
    def strip(ss):
        out = []
        for s in ss:
            if isinstance(s, Assert):
                continue
            if isinstance(s, If):
                out.append(If(s.c, strip(s.th), strip(s.el), s.ghost))
            elif isinstance(s, While):
                s2 = copy.copy(s); s2.body = strip(s.body); out.append(s2)
            else:
                out.append(s)
        return out
    it.run(strip(body), env)


def verify_ae(prob: AEProblem, inputs, top_k=4, max_combos=4000, time_budget=300, verbose=False):
    t0 = time.time()
    info = {'tried': []}
    plans = seq_plans(prob.A, prob.B)
    info['plans_total'] = len(plans)
    scored = []
    for idx, plan in enumerate(plans):
        woven = prob.weave(plan)
        space = prob.witness_space(woven['body'], woven['locals'])
        sites = sorted(space)
        combos = itertools.islice(_ranked_product([space[s] for s in sites]), max_combos)
        for rank, combo in enumerate(combos):
            if time.time() - t0 > time_budget / 2:
                break
            choice = dict(zip(sites, combo))
            w = prob.instantiate(woven, choice)
            if w is None:
                continue
            samples, ok, fails = run_ae(w, inputs, prob.aspecs, externs=prob.interp_externs)
            if fails or ok < max(2, len(inputs) // 4):
                continue
            types = {n: t for n, (t, g) in w['locals'].items()}
            for nm, _, _ in w['params']:
                types[nm] = [t for n, t, _ in w['params'] if n == nm][0]
            gv = guard_vars_of(w['body'])
            cands, sc = {}, 0
            for lp in all_loops(w['body']):
                smp = samples.get(lp.label, [])
                cs = mine(smp, types, gv, changed=assigned_vars(lp.body))
                sc += score_candidates(cs, assigned_vars(lp.body))
                cands[lp.label] = cs + mine_conditional(smp, types, antecedents_for(lp, w['body']), gv)
            # prefer non-prophecy, simpler witnesses
            nproph = sum(1 for c in combo if c[0] == 'prophecy')
            scored.append((nproph, -sc, rank, idx, plan, choice, w, cands))
            break  # first dynamically valid witness combo for this plan
    scored.sort(key=lambda x: x[:4])
    info['viable'] = len(scored)
    for (nproph, negsc, rank, idx, plan, choice, w, cands) in scored[:top_k]:
        if time.time() - t0 > time_budget:
            break
        res, text, rounds = houdini(w, prob.externs, cands)
        desc = {k: f'{v[0]}:{v[1]}' for k, v in choice.items()}
        info['tried'].append({'plan': plan.describe(), 'witness': desc, 'ok': res.ok,
                              'errors': [m for _, m in res.errors][:3]})
        if verbose:
            print('  ', plan.describe(), desc, res.ok, [m for _, m in res.errors][:2])
        if res.ok:
            info.update(plan=plan.describe(), witness=desc, dafny=text, time=time.time() - t0)
            return 'proved', info
    info['time'] = time.time() - t0
    return 'unknown', info


def _ranked_product(lists):
    """Cartesian product enumerated by increasing sum of indices."""
    if not lists:
        yield ()
        return
    n = len(lists)
    maxs = sum(len(l) - 1 for l in lists)
    for tot in range(maxs + 1):
        for idxs in _compositions(tot, [len(l) for l in lists]):
            yield tuple(l[i] for l, i in zip(lists, idxs))


def _compositions(tot, sizes):
    if len(sizes) == 1:
        if tot < sizes[0]:
            yield (tot,)
        return
    for i in range(min(tot, sizes[0] - 1) + 1):
        for rest in _compositions(tot - i, sizes[1:]):
            yield (i,) + rest
