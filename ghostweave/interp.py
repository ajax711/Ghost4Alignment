"""Concrete interpreter for the IR.  Used for (a) differential testing (finding non-equivalence
witnesses), (b) recording states at loop heads of woven programs for invariant mining, and
(c) cheap rejection of alignments before calling the verifier."""
from __future__ import annotations
import math
from .ir import *


class Diverge(Exception):
    pass


class Undefined(Exception):
    pass


def c_div(a, b):
    if b == 0:
        raise Undefined('div0')
    q = abs(a) // abs(b)
    return q if (a >= 0) == (b > 0) else -q


def c_mod(a, b):
    if b == 0:
        raise Undefined('mod0')
    return a - b * c_div(a, b)


def _u(f):
    def g(*a):
        try:
            r = f(*a)
        except (ValueError, OverflowError, ZeroDivisionError):
            raise Undefined('math')
        if isinstance(r, float) and (math.isnan(r) or math.isinf(r)):
            raise Undefined('nan')
        return r
    return g


EXTERN_IMPL = {
    'sqrt': _u(math.sqrt), 'log': _u(math.log), 'exp': _u(math.exp), 'sin': _u(math.sin), 'cos': _u(math.cos),
    'tan': _u(math.tan), 'atan': _u(math.atan), 'asin': _u(math.asin), 'acos': _u(math.acos),
    'floor': _u(lambda x: float(math.floor(x))), 'ceil': _u(lambda x: float(math.ceil(x))),
    'log10': _u(math.log10), 'sinh': _u(math.sinh), 'cosh': _u(math.cosh), 'tanh': _u(math.tanh),
    'pow': _u(math.pow), 'atan2': _u(math.atan2), 'fmod': _u(math.fmod),
    'band': lambda a, b: a & b, 'bor': lambda a, b: a | b, 'bxor': lambda a, b: a ^ b,
    'shl': lambda a, b: a << b if 0 <= b < 64 else 0, 'shr': lambda a, b: a >> b if 0 <= b < 64 else 0,
    'bnot': lambda a: ~a,
}


class Interp:
    def __init__(self, fuel=20000, externs=None, probe=None):
        self.fuel = fuel
        self.ext = dict(EXTERN_IMPL)
        if externs:
            self.ext.update(externs)
        self.probe = probe  # callback(label, env)

    def ev(self, e, env):
        if isinstance(e, Const):
            return e.val
        if isinstance(e, Var):
            if e.name not in env:
                raise Undefined('unset ' + e.name)
            return env[e.name]
        if isinstance(e, Bin):
            op = e.op
            if op == '&&':
                return self.ev(e.l, env) and self.ev(e.r, env)
            if op == '||':
                return self.ev(e.l, env) or self.ev(e.r, env)
            if op == '==>':
                return (not self.ev(e.l, env)) or self.ev(e.r, env)
            a = self.ev(e.l, env)
            b = self.ev(e.r, env)
            if op == '+':
                return a + b
            if op == '-':
                return a - b
            if op == '*':
                r = a * b
                if isinstance(r, int) and abs(r) > 1 << 200:
                    raise Undefined('huge')
                return r
            if op == '/':
                if e.ty == INT:
                    return c_div(a, b)
                if b == 0:
                    raise Undefined('rdiv0')
                return a / b
            if op == '%':
                return c_mod(a, b)
            if op == '<':
                return a < b
            if op == '<=':
                return a <= b
            if op == '>':
                return a > b
            if op == '>=':
                return a >= b
            if op == '==':
                return a == b
            if op == '!=':
                return a != b
            if op == '<==>':
                return bool(a) == bool(b)
            raise Undefined('op ' + op)
        if isinstance(e, Un):
            v = self.ev(e.e, env)
            return -v if e.op == 'neg' else (not v)
        if isinstance(e, Ite):
            return self.ev(e.a, env) if self.ev(e.c, env) else self.ev(e.b, env)
        if isinstance(e, Call):
            args = [self.ev(a, env) for a in e.args]
            if e.f not in self.ext:
                raise Undefined('extern ' + e.f)
            r = self.ext[e.f](*args)
            if e.ty == REAL:
                r = float(r)
            return r
        if isinstance(e, Cast):
            v = self.ev(e.e, env)
            if e.ty == INT:
                if isinstance(v, float) and (math.isnan(v) or math.isinf(v)):
                    raise Undefined('cast')
                return int(v)  # truncation toward zero
            if e.ty == REAL:
                return float(v)
            return v
        if isinstance(e, Idx):
            a = self.ev(e.arr, env)
            i = self.ev(e.i, env)
            if not (0 <= i < len(a)):
                raise Undefined('oob')
            return a[i]
        if isinstance(e, Upd):
            a = self.ev(e.arr, env)
            i = self.ev(e.i, env)
            if not (0 <= i < len(a)):
                raise Undefined('oob')
            v = self.ev(e.v, env)
            return a[:i] + (v,) + a[i + 1:]
        if isinstance(e, Len):
            return len(self.ev(e.arr, env))
        if isinstance(e, SeqLit):
            return default_seq(e.n, e.elem)
        if isinstance(e, Raw):
            return True
        raise TypeError(e)

    def run(self, ss, env):
        for s in ss:
            self.step(s, env)

    def step(self, s, env):
        if isinstance(s, Assign):
            env[s.name] = self.ev(s.e, env)
        elif isinstance(s, Havoc):
            env.setdefault(s.name, None)
            if env[s.name] is None:
                env[s.name] = 0
        elif isinstance(s, If):
            self.run(s.th if self.ev(s.c, env) else s.el, env)
        elif isinstance(s, While):
            while True:
                if self.probe and s.label:
                    self.probe(s.label, env)
                self.fuel -= 1
                if self.fuel < 0:
                    raise Diverge()
                if not self.ev(s.c, env):
                    break
                self.run(s.body, env)
            if self.probe and s.label:
                self.probe(s.label + '#exit', env)
        elif isinstance(s, Assert):
            if not self.ev(s.e, env):
                raise AssertionError(s.tag)
        elif isinstance(s, Assume):
            if not self.ev(s.e, env):
                raise Undefined('assume')
        elif isinstance(s, Probe):
            if self.probe:
                self.probe(s.label, env)
        else:
            raise TypeError(s)


def default_seq(n, elem):
    if isinstance(elem, tuple) and elem[0] == 'seqlit':
        return tuple(default_seq(elem[1], elem[2]) for _ in range(n))
    z = 0.0 if elem == REAL else (False if elem == BOOL else 0)
    return tuple(z for _ in range(n))


def rec_impls(prog, suffix=''):
    """Concrete implementations of rec_<f> for the recursive functions of a Program."""
    impls = {}      # unsuffixed: used inside the recursive bodies themselves
    depth = [0]

    def mk(f, sub):
        def call(*args):
            depth[0] += 1
            try:
                if depth[0] > 300:
                    raise Undefined('recursion depth')
                env = {n: a for (n, _), a in zip(sub.func.params, args)}
                it = Interp(20000, externs=impls)
                it.run(sub.func.body, env)
                return env.get('ret')
            finally:
                depth[0] -= 1
        return call
    for f, sub in getattr(prog, 'rec_funcs', {}).items():
        impls['rec_' + f] = mk(f, sub)
    return {k + suffix: v for k, v in impls.items()}


def run_func(func, inputs, fuel=20000, havoc_default=0, externs=None):
    """Run a Func on a dict of inputs. Returns observable output tuple."""
    env = dict(inputs)
    it = Interp(fuel, externs=externs)
    it.run(func.body, env)
    out = []
    if func.ret_ty is not None:
        out.append(env.get('ret'))
    for p in func.out_params:
        out.append(env.get(p))
    return tuple(out)
