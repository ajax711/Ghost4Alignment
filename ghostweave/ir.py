"""Small imperative IR shared by the C frontend, the interpreter, the weaver and the Dafny backend.

Types: 'int', 'real', 'bool', ('seq', T).  Integers are mathematical (unbounded), doubles are reals.
Every statement carries a `ghost` flag; the weaver sets it on statements that come from P2.
"""
from __future__ import annotations
from dataclasses import dataclass, field
from typing import Any, List, Optional

INT, REAL, BOOL = 'int', 'real', 'bool'


def seq_of(t):
    return ('seq', t)


def is_seq(t):
    return isinstance(t, tuple) and t[0] == 'seq'


# ---------------------------------------------------------------- expressions
class Expr:
    ty: Any


@dataclass
class Var(Expr):
    name: str
    ty: Any


@dataclass
class Const(Expr):
    val: Any
    ty: Any


@dataclass
class Bin(Expr):
    op: str  # + - * / % < <= > >= == != && || ==> <==>  band bor bxor shl shr
    l: Expr
    r: Expr
    ty: Any


@dataclass
class Un(Expr):
    op: str  # neg, not
    e: Expr
    ty: Any


@dataclass
class Ite(Expr):
    c: Expr
    a: Expr
    b: Expr
    ty: Any


@dataclass
class Call(Expr):
    """Pure call to an external (uninterpreted in Dafny, concrete in the interpreter) function."""
    f: str
    args: List[Expr]
    ty: Any


@dataclass
class Cast(Expr):
    e: Expr
    ty: Any


@dataclass
class Idx(Expr):
    arr: Expr
    i: Expr
    ty: Any


@dataclass
class Upd(Expr):
    arr: Expr
    i: Expr
    v: Expr
    ty: Any


@dataclass
class Len(Expr):
    arr: Expr
    ty: Any = INT


@dataclass
class SeqLit(Expr):
    n: int
    elem: Any
    ty: Any


@dataclass
class Raw(Expr):
    """Verbatim Dafny boolean expression (e.g. a user-supplied relational pre/postcondition with
    quantifiers).  The interpreter treats it as true."""
    text: str
    ty: Any = BOOL


# ---------------------------------------------------------------- statements
class Stmt:
    ghost: bool = False


@dataclass
class Assign(Stmt):
    name: str
    e: Expr
    ghost: bool = False


@dataclass
class Havoc(Stmt):
    name: str
    ghost: bool = False


@dataclass
class If(Stmt):
    c: Expr
    th: List[Stmt]
    el: List[Stmt]
    ghost: bool = False


@dataclass
class While(Stmt):
    c: Expr
    body: List[Stmt]
    lid: str = ''
    invs: List[Expr] = field(default_factory=list)
    dec: Optional[Expr] = None
    ghost: bool = False
    # filled by the weaver for real loops that carry ghost steps: name of the trace label
    label: str = ''


@dataclass
class Assert(Stmt):
    e: Expr
    tag: str = ''
    ghost: bool = False


@dataclass
class Assume(Stmt):
    e: Expr
    ghost: bool = False


@dataclass
class Probe(Stmt):
    """No-op marker used by the interpreter to record states (loop heads)."""
    label: str
    ghost: bool = False


# ---------------------------------------------------------------- helpers
def T(b):
    return Const(True, BOOL)


TRUE = Const(True, BOOL)
FALSE = Const(False, BOOL)


def mk_and(a, b):
    if isinstance(a, Const) and a.val is True:
        return b
    if isinstance(b, Const) and b.val is True:
        return a
    return Bin('&&', a, b, BOOL)


def mk_not(a):
    if isinstance(a, Un) and a.op == 'not':
        return a.e
    return Un('not', a, BOOL)


def mk_or(a, b):
    if isinstance(a, Const) and a.val is False:
        return b
    if isinstance(b, Const) and b.val is False:
        return a
    return Bin('||', a, b, BOOL)


def expr_vars(e, acc=None):
    if acc is None:
        acc = set()
    if isinstance(e, Var):
        acc.add(e.name)
    elif isinstance(e, Bin):
        expr_vars(e.l, acc); expr_vars(e.r, acc)
    elif isinstance(e, Un):
        expr_vars(e.e, acc)
    elif isinstance(e, Ite):
        expr_vars(e.c, acc); expr_vars(e.a, acc); expr_vars(e.b, acc)
    elif isinstance(e, Call):
        for a in e.args:
            expr_vars(a, acc)
    elif isinstance(e, Cast):
        expr_vars(e.e, acc)
    elif isinstance(e, Idx):
        expr_vars(e.arr, acc); expr_vars(e.i, acc)
    elif isinstance(e, Upd):
        expr_vars(e.arr, acc); expr_vars(e.i, acc); expr_vars(e.v, acc)
    elif isinstance(e, Len):
        expr_vars(e.arr, acc)
    return acc


def rename_expr(e, f):
    """f: name -> name"""
    if isinstance(e, Var):
        return Var(f(e.name), e.ty)
    if isinstance(e, (Const, SeqLit, Raw)):
        return e
    if isinstance(e, Bin):
        return Bin(e.op, rename_expr(e.l, f), rename_expr(e.r, f), e.ty)
    if isinstance(e, Un):
        return Un(e.op, rename_expr(e.e, f), e.ty)
    if isinstance(e, Ite):
        return Ite(rename_expr(e.c, f), rename_expr(e.a, f), rename_expr(e.b, f), e.ty)
    if isinstance(e, Call):
        return Call(e.f, [rename_expr(a, f) for a in e.args], e.ty)
    if isinstance(e, Cast):
        return Cast(rename_expr(e.e, f), e.ty)
    if isinstance(e, Idx):
        return Idx(rename_expr(e.arr, f), rename_expr(e.i, f), e.ty)
    if isinstance(e, Upd):
        return Upd(rename_expr(e.arr, f), rename_expr(e.i, f), rename_expr(e.v, f), e.ty)
    if isinstance(e, Len):
        return Len(rename_expr(e.arr, f), e.ty)
    raise TypeError(e)


def rename_stmts(ss, f, ghost=None):
    out = []
    for s in ss:
        g = s.ghost if ghost is None else ghost
        if isinstance(s, Assign):
            out.append(Assign(f(s.name), rename_expr(s.e, f), g))
        elif isinstance(s, Havoc):
            out.append(Havoc(f(s.name), g))
        elif isinstance(s, If):
            out.append(If(rename_expr(s.c, f), rename_stmts(s.th, f, ghost), rename_stmts(s.el, f, ghost), g))
        elif isinstance(s, While):
            out.append(While(rename_expr(s.c, f), rename_stmts(s.body, f, ghost), s.lid,
                             [rename_expr(i, f) for i in s.invs], rename_expr(s.dec, f) if s.dec else None, g, s.label))
        elif isinstance(s, Assert):
            out.append(Assert(rename_expr(s.e, f), s.tag, g))
        elif isinstance(s, Assume):
            out.append(Assume(rename_expr(s.e, f), g))
        elif isinstance(s, Probe):
            out.append(Probe(s.label, g))
        else:
            raise TypeError(s)
    return out


def assigned_vars(ss, acc=None):
    if acc is None:
        acc = set()
    for s in ss:
        if isinstance(s, (Assign, Havoc)):
            acc.add(s.name)
        elif isinstance(s, If):
            assigned_vars(s.th, acc); assigned_vars(s.el, acc)
        elif isinstance(s, While):
            assigned_vars(s.body, acc)
    return acc


def loops_in(ss):
    out = []
    for s in ss:
        if isinstance(s, While):
            out.append(s)
        elif isinstance(s, If):
            out += loops_in(s.th) + loops_in(s.el)
    return out


def count_loops(ss):
    n = 0
    for s in ss:
        if isinstance(s, While):
            n += 1 + count_loops(s.body)
        elif isinstance(s, If):
            n += count_loops(s.th) + count_loops(s.el)
    return n


@dataclass
class Func:
    name: str
    params: List[tuple]          # (name, type)
    ret_ty: Any                  # type or None (void)
    body: List[Stmt]
    locals: dict                 # name -> type (includes params and 'ret')
    out_params: List[str] = field(default_factory=list)  # array params observable by the caller


@dataclass
class Program:
    """A single (fully inlined) entry function plus the external functions it uses."""
    func: Func
    externs: dict                # name -> (arg types, ret type)


def map_calls_expr(e, f):
    """f: Call -> Expr (or None to keep); applied bottom-up."""
    if isinstance(e, (Var, Const, SeqLit, Raw)):
        return e
    if isinstance(e, Bin):
        return Bin(e.op, map_calls_expr(e.l, f), map_calls_expr(e.r, f), e.ty)
    if isinstance(e, Un):
        return Un(e.op, map_calls_expr(e.e, f), e.ty)
    if isinstance(e, Ite):
        return Ite(map_calls_expr(e.c, f), map_calls_expr(e.a, f), map_calls_expr(e.b, f), e.ty)
    if isinstance(e, Call):
        c = Call(e.f, [map_calls_expr(a, f) for a in e.args], e.ty)
        r = f(c)
        return c if r is None else r
    if isinstance(e, Cast):
        return Cast(map_calls_expr(e.e, f), e.ty)
    if isinstance(e, Idx):
        return Idx(map_calls_expr(e.arr, f), map_calls_expr(e.i, f), e.ty)
    if isinstance(e, Upd):
        return Upd(map_calls_expr(e.arr, f), map_calls_expr(e.i, f), map_calls_expr(e.v, f), e.ty)
    if isinstance(e, Len):
        return Len(map_calls_expr(e.arr, f), e.ty)
    raise TypeError(e)


def map_calls_stmts(ss, f):
    out = []
    for s in ss:
        if isinstance(s, Assign):
            out.append(Assign(s.name, map_calls_expr(s.e, f), s.ghost))
        elif isinstance(s, If):
            out.append(If(map_calls_expr(s.c, f), map_calls_stmts(s.th, f), map_calls_stmts(s.el, f), s.ghost))
        elif isinstance(s, While):
            out.append(While(map_calls_expr(s.c, f), map_calls_stmts(s.body, f), s.lid, list(s.invs), s.dec, s.ghost, s.label))
        elif isinstance(s, Assert):
            out.append(Assert(map_calls_expr(s.e, f), s.tag, s.ghost))
        elif isinstance(s, Assume):
            out.append(Assume(map_calls_expr(s.e, f), s.ghost))
        else:
            out.append(s)
    return out


def rename_calls(ss, mapping):
    return map_calls_stmts(ss, lambda c: Call(mapping[c.f], c.args, c.ty) if c.f in mapping else None)
