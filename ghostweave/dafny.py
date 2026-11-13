"""Emit a woven program as an ordinary (unary) Dafny method and run the stock Dafny verifier."""
from __future__ import annotations
import os
import re
import shutil
import subprocess
import tempfile
from decimal import Decimal
from .ir import *

DAFNY = shutil.which('dafny') or os.path.expanduser('~/.dotnet/tools/dafny')

PRELUDE = """
function cabs(x: int): int { if x < 0 then -x else x }
function divz(a: int): int
function modz(a: int): int
function cdiv(a: int, b: int): int { if b == 0 then divz(a) else if (a >= 0) == (b > 0) then cabs(a) / cabs(b) else -(cabs(a) / cabs(b)) }
function cmod(a: int, b: int): int { if b == 0 then modz(a) else a - b * cdiv(a, b) }
function rdivz(a: real): real
function rdiv(a: real, b: real): real { if b == 0.0 then rdivz(a) else a / b }
function trunc(x: real): int { if x >= 0.0 then x.Floor else -((-x).Floor) }
function oob<T(0)>(i: int): T
function rd<T(0)>(s: seq<T>, i: int): T { if 0 <= i < |s| then s[i] else oob(i) }
function wr<T>(s: seq<T>, i: int, v: T): seq<T> { if 0 <= i < |s| then s[i := v] else s }
"""


def dty(t):
    if t == INT:
        return 'int'
    if t == REAL:
        return 'real'
    if t == BOOL:
        return 'bool'
    if is_seq(t):
        return f'seq<{dty(t[1])}>'
    raise ValueError(t)


def real_lit(v):
    d = Decimal(repr(float(v)))
    s = format(d, 'f')
    if '.' not in s:
        s += '.0'
    if s.startswith('-'):
        return f'(-{s[1:]})'
    return s


def seqlit(n, elem):
    if isinstance(elem, tuple) and elem[0] == 'seqlit':
        return f'seq({n}, _ => {seqlit(elem[1], elem[2])})'
    z = {INT: '0', REAL: '0.0', BOOL: 'false'}[elem]
    return f'seq({n}, _ => {z})'


CALL_ALIAS = {}   # set during emission: identifies side-specific UFs proven equal (mutual summaries)


def ex(e) -> str:
    if isinstance(e, Var):
        return e.name
    if isinstance(e, Const):
        if e.ty == BOOL:
            return 'true' if e.val else 'false'
        if e.ty == REAL:
            return real_lit(e.val)
        return str(e.val) if e.val >= 0 else f'({e.val})'
    if isinstance(e, Bin):
        a, b = ex(e.l), ex(e.r)
        if e.op == '/':
            return f'cdiv({a}, {b})' if e.ty == INT else f'rdiv({a}, {b})'
        if e.op == '%':
            return f'cmod({a}, {b})'
        return f'({a} {e.op} {b})'
    if isinstance(e, Un):
        return f'(-{ex(e.e)})' if e.op == 'neg' else f'(!{ex(e.e)})'
    if isinstance(e, Ite):
        return f'(if {ex(e.c)} then {ex(e.a)} else {ex(e.b)})'
    if isinstance(e, Call):
        return f'{CALL_ALIAS.get(e.f, e.f)}({", ".join(ex(a) for a in e.args)})'
    if isinstance(e, Cast):
        if e.ty == INT:
            return f'trunc({ex(e.e)})'
        if e.ty == REAL:
            return f'({ex(e.e)} as real)'
        return ex(e.e)
    if isinstance(e, Idx):
        return f'rd({ex(e.arr)}, {ex(e.i)})'
    if isinstance(e, Upd):
        return f'wr({ex(e.arr)}, {ex(e.i)}, {ex(e.v)})'
    if isinstance(e, Len):
        return f'|{ex(e.arr)}|'
    if isinstance(e, SeqLit):
        return seqlit(e.n, e.elem)
    if isinstance(e, Raw):
        return '(' + e.text + ')'
    raise TypeError(e)


class Emitter:
    def __init__(self):
        self.lines = []
        self.inv_lines = {}   # line number (1-based) -> (loop id, invariant index)
        self.assert_lines = {}

    def emit(self, s, ind):
        p = '  ' * ind
        if isinstance(s, Assign):
            self.lines.append(f'{p}{s.name} := {ex(s.e)};')
        elif isinstance(s, Havoc):
            self.lines.append(f'{p}{s.name} :| true;')
        elif isinstance(s, If):
            self.lines.append(f'{p}if {ex(s.c)} {{')
            for t in s.th:
                self.emit(t, ind + 1)
            if s.el:
                self.lines.append(f'{p}}} else {{')
                for t in s.el:
                    self.emit(t, ind + 1)
            self.lines.append(f'{p}}}')
        elif isinstance(s, While):
            self.lines.append(f'{p}while {ex(s.c)}')
            for k, inv in enumerate(s.invs):
                self.lines.append(f'{p}  invariant {ex(inv)}')
                self.inv_lines[len(self.lines)] = (s.lid, k)
            if s.dec is not None:
                self.lines.append(f'{p}  decreases {ex(s.dec)}')
            elif not s.ghost:
                self.lines.append(f'{p}  decreases *')
            self.lines.append(f'{p}{{')
            for t in s.body:
                self.emit(t, ind + 1)
            self.lines.append(f'{p}}}')
        elif isinstance(s, Assert):
            self.lines.append(f'{p}assert {ex(s.e)};')
            self.assert_lines[len(self.lines)] = s.tag
        elif isinstance(s, Assume):
            self.lines.append(f'{p}assume {{:axiom}} {ex(s.e)};')
        elif isinstance(s, Probe):
            pass
        else:
            raise TypeError(s)


def emit_method(woven, externs, header_comment=''):
    """woven: dict with keys
         params: list of (name, ty, ghost)    -- method inputs
         outs: list of (name, ty, ghost)      -- method outputs (assigned at the end)
         requires: list[Expr], ensures: list[Expr]
         locals: dict name -> (ty, ghost)
         body: list[Stmt]
    Returns (text, emitter)."""
    em = Emitter()
    CALL_ALIAS.clear()
    CALL_ALIAS.update(woven.get('call_alias', {}))
    em.lines += [l for l in PRELUDE.strip('\n').split('\n')]
    emitted = set()
    for f, (ats, rt) in sorted(externs.items()):
        f = CALL_ALIAS.get(f, f)
        if f in emitted:
            continue
        emitted.add(f)
        args = ', '.join(f'x{i}: {dty(t)}' for i, t in enumerate(ats))
        em.lines.append(f'function {f}({args}): {dty(rt)}')
    if header_comment:
        for l in header_comment.strip().split('\n'):
            em.lines.append('// ' + l)
    ps = ', '.join(('ghost ' if g else '') + f'{n}: {dty(t)}' for n, t, g in woven['params'])
    os_ = ', '.join(('ghost ' if g else '') + f'{n}: {dty(t)}' for n, t, g in woven['outs'])
    em.lines.append(f'method Woven({ps})' + (f' returns ({os_})' if os_ else ''))
    for r in woven['requires']:
        em.lines.append(f'  requires {ex(r)}')
    for e in woven['ensures']:
        em.lines.append(f'  ensures {ex(e)}')
        em.assert_lines[len(em.lines)] = 'post'
    em.lines.append('  decreases *')
    em.lines.append('{')
    outnames = {n for n, _, _ in woven['outs']}
    for n, (t, g) in sorted(woven['locals'].items()):
        if n in outnames:
            continue
        em.lines.append(f'  {"ghost " if g else ""}var {n}: {dty(t)} :| true;')
    for s in woven['body']:
        em.emit(s, 1)
    em.lines.append('}')
    return '\n'.join(em.lines) + '\n', em


ERR_RE = re.compile(r'^(.*?)\((\d+),(\d+)\): (Error|Warning)[^:]*: (.*)$')


class DafnyResult:
    def __init__(self, ok, errors, raw, timeout=False):
        self.ok, self.errors, self.raw, self.timeout = ok, errors, raw, timeout

    def __repr__(self):
        return f'DafnyResult(ok={self.ok}, errors={self.errors[:4]}, timeout={self.timeout})'


def run_dafny(text, timeout=120, vc_limit=60, workdir=None, keep=None):
    fd, path = tempfile.mkstemp(suffix='.dfy', dir=workdir)
    with os.fdopen(fd, 'w') as f:
        f.write(text)
    if keep:
        shutil.copy(path, keep)
    try:
        cp = subprocess.run([DAFNY, 'verify', '--allow-warnings', '--cores', '1', '--isolate-assertions',
                             f'--verification-time-limit', str(vc_limit), path],
                            capture_output=True, text=True, timeout=timeout)
        out = cp.stdout + cp.stderr
    except subprocess.TimeoutExpired:
        os.unlink(path)
        return DafnyResult(False, [], 'TIMEOUT', timeout=True)
    os.unlink(path)
    errors = []
    for line in out.split('\n'):
        m = ERR_RE.match(line.strip())
        if m and m.group(4) == 'Error' and os.path.basename(m.group(1)) == os.path.basename(path):
            errors.append((int(m.group(2)), m.group(5)))
    ok = bool(re.search(r'finished with \d+ verified, 0 errors', out)) and not errors
    to = 'timed out' in out
    if not ok and not errors and not to:
        # resolution / type errors are printed differently
        for line in out.split('\n'):
            if 'Error' in line or 'error' in line:
                errors.append((0, line.strip()))
    return DafnyResult(ok, errors, out, timeout=to)
