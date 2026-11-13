"""C (EqBench / KestRel subset) -> IR.

* parses with pycparser after stripping #include and running cpp
* inlines every non-recursive call (pointer / array arguments are passed by alias)
* recursive calls are abstracted by an uninterpreted function `rec_<f>` (mutual-summary rule);
  the driver discharges the matching obligation separately
* eliminates return / break / continue into structured code with flags
* doubles -> reals, ints -> mathematical integers, math library calls -> uninterpreted functions
"""
from __future__ import annotations
import re
import subprocess
from pycparser import c_parser, c_ast
from .ir import *


class Unsupported(Exception):
    pass


MATH_REAL1 = {'sqrt', 'log', 'exp', 'sin', 'cos', 'tan', 'atan', 'asin', 'acos', 'floor', 'ceil',
              'log10', 'sinh', 'cosh', 'tanh', 'fabs'}
MATH_REAL2 = {'pow', 'atan2', 'fmod', 'fmax', 'fmin'}
IGNORED_CALLS = {'_invariant', 'printf', 'puts', 'putchar', 'fprintf', 'exit', 'assert', 'srand'}


def preprocess(src: str) -> str:
    src = re.sub(r'^\s*#\s*include.*$', '', src, flags=re.M)
    src = '#define M_PI 3.14159265358979323846\n#define M_E 2.7182818284590452354\n' + src
    out = subprocess.run(['cpp', '-P', '-w', '-'], input=src, capture_output=True, text=True)
    if out.returncode != 0:
        raise Unsupported('cpp: ' + out.stderr[:200])
    text = out.stdout
    # pycparser does not know stdbool / a few builtins
    pre = 'typedef int bool; typedef int size_t; typedef int FILE;\n'
    text = text.replace('true', '1').replace('false', '0') if False else text
    return pre + text


# ------------------------------------------------------------------ markers used before jump elimination
class _Ret(Stmt):
    def __init__(self, e):
        self.e = e
        self.ghost = False


class _Brk(Stmt):
    ghost = False


class _Cont(Stmt):
    ghost = False


def c_type(node):
    """pycparser type node -> IR type (pointers become sequences)."""
    if isinstance(node, c_ast.TypeDecl):
        if isinstance(node.type, c_ast.IdentifierType):
            names = node.type.names
            if any(n in ('double', 'float') for n in names):
                return REAL
            if 'bool' in names or '_Bool' in names:
                return BOOL
            if 'void' in names:
                return None
            return INT
        if isinstance(node.type, c_ast.Struct):
            raise Unsupported('struct')
        raise Unsupported('type ' + type(node.type).__name__)
    if isinstance(node, (c_ast.ArrayDecl, c_ast.PtrDecl)):
        inner = c_type(node.type)
        return seq_of(inner)
    if isinstance(node, c_ast.FuncDecl):
        raise Unsupported('function pointer')
    if isinstance(node, c_ast.Typename):
        return c_type(node.type)
    raise Unsupported('type ' + type(node).__name__)


def coerce(e: Expr, ty):
    """Convert expression to type ty with C semantics."""
    if e.ty == ty or ty is None:
        return e
    if ty == BOOL:
        if e.ty == INT:
            return Bin('!=', e, Const(0, INT), BOOL)
        if e.ty == REAL:
            return Bin('!=', e, Const(0.0, REAL), BOOL)
    if ty == INT:
        if e.ty == BOOL:
            return Ite(e, Const(1, INT), Const(0, INT), INT)
        if e.ty == REAL:
            return Cast(e, INT)  # truncation toward zero
    if ty == REAL:
        if e.ty == INT:
            if isinstance(e, Const):
                return Const(float(e.val), REAL)
            return Cast(e, REAL)
        if e.ty == BOOL:
            return Ite(e, Const(1.0, REAL), Const(0.0, REAL), REAL)
    if is_seq(ty) and is_seq(e.ty):
        return e
    raise Unsupported(f'coerce {e.ty} -> {ty}')


def arith_ty(a, b):
    if a == REAL or b == REAL:
        return REAL
    return INT


class Frontend:
    def __init__(self, src: str, tag: str, choice_funcs=()):
        self.choice_funcs = set(choice_funcs)
        self.tag = tag  # used to make recursive-function UF names distinct when needed
        text = preprocess(src)
        try:
            self.ast = c_parser.CParser().parse(text)
        except Exception as ex:  # pragma: no cover
            raise Unsupported('parse: ' + str(ex)[:120])
        self.funcs = {}
        self.protos = {}
        self.globals = []  # (name, ty, init node)
        for ext in self.ast.ext:
            if isinstance(ext, c_ast.FuncDef):
                self.funcs[ext.decl.name] = ext
            elif isinstance(ext, c_ast.Decl):
                if isinstance(ext.type, c_ast.FuncDecl):
                    self.protos[ext.name] = ext
                elif ext.name is not None:
                    self.globals.append((ext.name, c_type(ext.type), ext.init, ext.type))
            elif isinstance(ext, c_ast.Typedef):
                pass
        self.counter = 0
        self.externs = {}
        self.recursive_used = set()

    def fresh(self, base):
        self.counter += 1
        return f'{base}_{self.counter}'

    # ------------------------------------------------------------------ entry
    def lower_entry(self, fname: str, global_inputs=True) -> Program:
        if fname not in self.funcs:
            raise Unsupported('no function ' + fname)
        fd = self.funcs[fname]
        self.locals = {}
        env = {}
        params = []
        pre = []
        # globals
        for (gname, gty, ginit, gnode) in self.globals:
            self.locals[gname] = gty
            env[gname] = ('var', gname, gty)
            if ginit is not None:
                stmts, e = self.lower_init(ginit, gty, env, gnode)
                pre += stmts + [Assign(gname, e)]
            elif is_seq(gty):
                n = self.array_len(gnode)
                pre.append(Assign(gname, SeqLit(n, gty[1], gty)))
            elif global_inputs:
                params.append((gname, gty))
            else:
                pre.append(Assign(gname, self.zero(gty)))
        out_params = []
        for p in self.param_decls(fd):
            pty = c_type(p.type)
            self.locals[p.name] = pty
            env[p.name] = ('var', p.name, pty)
            params.append((p.name, pty))
            if is_seq(pty):
                out_params.append(p.name)
        ret_ty = c_type(fd.decl.type.type)
        self.call_stack = [fname]
        body = self.lower_function_body(fd, env, 'ret', ret_ty)
        if ret_ty is not None:
            self.locals['ret'] = ret_ty
        func = Func(fname, params, ret_ty, pre + body, dict(self.locals), out_params)
        return Program(func, dict(self.externs))

    def param_decls(self, fd):
        args = fd.decl.type.args
        if args is None:
            return []
        out = []
        for p in args.params:
            if isinstance(p, c_ast.EllipsisParam):
                raise Unsupported('varargs')
            if isinstance(p, c_ast.Typename) and c_type(p.type) is None:
                continue  # f(void)
            out.append(p)
        return out

    def zero(self, ty):
        if ty == REAL:
            return Const(0.0, REAL)
        if ty == BOOL:
            return Const(False, BOOL)
        if ty == INT:
            return Const(0, INT)
        raise Unsupported('zero of ' + str(ty))

    def array_len(self, node):
        if isinstance(node, c_ast.ArrayDecl) and node.dim is not None:
            if isinstance(node.dim, c_ast.ID) and node.dim.name in getattr(self, 'consts', {}):
                return self.consts[node.dim.name]
            if isinstance(node.dim, c_ast.Constant):
                return int(node.dim.value.rstrip('uUlL'), 0)
            if isinstance(node.dim, c_ast.BinaryOp):
                return int(eval(self.const_str(node.dim)))
        raise Unsupported('array length')

    def const_str(self, n):
        if isinstance(n, c_ast.Constant):
            return n.value.rstrip('uUlL')
        if isinstance(n, c_ast.BinaryOp):
            return '(' + self.const_str(n.left) + n.op + self.const_str(n.right) + ')'
        raise Unsupported('const expr')

    # ------------------------------------------------------------------ functions
    def lower_function_body(self, fd, env, retvar, ret_ty):
        self.loop_flags = []
        raw = self.lower_stmt(fd.body, dict(env), retvar, ret_ty)
        return eliminate_jumps(raw, retvar, self)

    def declare(self, cname, ty, env, ghost_base=None):
        base = cname
        name = base
        if name in self.locals:
            name = self.fresh(base)
        self.locals[name] = ty
        env[cname] = ('var', name, ty)
        return name

    # ------------------------------------------------------------------ statements
    def lower_block(self, items, env, retvar, ret_ty):
        out = []
        for it in items or []:
            out += self.lower_stmt(it, env, retvar, ret_ty)
        return out

    def lower_stmt(self, s, env, retvar, ret_ty):
        if s is None:
            return []
        if isinstance(s, c_ast.Compound):
            return self.lower_block(s.block_items, dict(env), retvar, ret_ty) if False else self._compound(s, env, retvar, ret_ty)
        if isinstance(s, c_ast.Decl):
            return self.lower_decl(s, env)
        if isinstance(s, c_ast.DeclList):
            out = []
            for d in s.decls:
                out += self.lower_decl(d, env)
            return out
        if isinstance(s, c_ast.Assignment) or isinstance(s, c_ast.UnaryOp) or isinstance(s, c_ast.FuncCall) \
                or isinstance(s, c_ast.ExprList) or isinstance(s, c_ast.ID) or isinstance(s, c_ast.Constant) \
                or isinstance(s, c_ast.BinaryOp) or isinstance(s, c_ast.TernaryOp) or isinstance(s, c_ast.Cast):
            pre, _ = self.lower_expr(s, env, discard=True)
            return pre
        if isinstance(s, c_ast.EmptyStatement):
            return []
        if isinstance(s, c_ast.Return):
            if s.expr is None:
                return [_Ret(None)]
            pre, e = self.lower_expr(s.expr, env)
            if ret_ty is not None:
                e = coerce(e, ret_ty)
            return pre + [_Ret(e)]
        if isinstance(s, c_ast.If):
            pre, c = self.lower_expr(s.cond, env)
            th = self.lower_stmt(s.iftrue, dict(env), retvar, ret_ty)
            el = self.lower_stmt(s.iffalse, dict(env), retvar, ret_ty)
            return pre + [If(coerce(c, BOOL), th, el)]
        if isinstance(s, c_ast.While):
            return self.lower_loop(None, s.cond, None, s.stmt, env, retvar, ret_ty)
        if isinstance(s, c_ast.For):
            env2 = dict(env)
            init = []
            if s.init is not None:
                init = self.lower_stmt(s.init, env2, retvar, ret_ty)
            return init + self.lower_loop(None, s.cond, s.next, s.stmt, env2, retvar, ret_ty)
        if isinstance(s, c_ast.DoWhile):
            return self.lower_loop('do', s.cond, None, s.stmt, env, retvar, ret_ty)
        if isinstance(s, c_ast.Break):
            return [_Brk()]
        if isinstance(s, c_ast.Continue):
            return [_Cont()]
        if isinstance(s, c_ast.Switch):
            return self.lower_switch(s, env, retvar, ret_ty)
        raise Unsupported('stmt ' + type(s).__name__)

    def _compound(self, s, env, retvar, ret_ty):
        env2 = dict(env)
        out = []
        for it in s.block_items or []:
            out += self.lower_stmt(it, env2, retvar, ret_ty)
        return out

    def lower_loop(self, kind, cond, nxt, body, env, retvar, ret_ty):
        env2 = dict(env)
        b = self.lower_stmt(body, env2, retvar, ret_ty)
        nx = []
        if nxt is not None:
            nx, _ = self.lower_expr(nxt, env2, discard=True)
        if cond is None:
            cpre, c = [], TRUE
        else:
            cpre, c = self.lower_expr(cond, env2)
            c = coerce(c, BOOL)
        lp = _Loop(c, cpre, b, nx, kind == 'do')
        return [lp]

    def lower_switch(self, s, env, retvar, ret_ty):
        pre, v = self.lower_expr(s.cond, env)
        tmp = self.declare(self.fresh('sw'), v.ty, env)
        out = pre + [Assign(tmp, v)]
        cases = s.stmt.block_items or []
        # simple form: every case ends with break / return; default last
        chain = []
        for c in cases:
            if isinstance(c, c_ast.Case):
                _, ce = self.lower_expr(c.expr, env)
                stmts = list(c.stmts or [])
                chain.append((ce, stmts))
            elif isinstance(c, c_ast.Default):
                chain.append((None, list(c.stmts or [])))
            else:
                raise Unsupported('switch body')
        res = []
        for ce, stmts in reversed(chain):
            if stmts and isinstance(stmts[-1], c_ast.Break):
                stmts = stmts[:-1]
            elif stmts and not isinstance(stmts[-1], c_ast.Return):
                raise Unsupported('switch fallthrough')
            body = []
            env2 = dict(env)
            for it in stmts:
                body += self.lower_stmt(it, env2, retvar, ret_ty)
            if ce is None:
                res = body
            else:
                res = [If(Bin('==', Var(tmp, v.ty), ce, BOOL), body, res)]
        return out + res

    def lower_decl(self, d, env):
        if isinstance(d.type, c_ast.FuncDecl):
            return []
        ty = c_type(d.type)
        name = self.declare(d.name, ty, env)
        if ty == INT and isinstance(d.init, c_ast.Constant) and d.init.type == 'int':
            if not hasattr(self, 'consts'):
                self.consts = {}
            self.consts[d.name] = int(d.init.value.rstrip('uUlL'), 0)
        if d.init is not None:
            pre, e = self.lower_init(d.init, ty, env, d.type)
            return pre + [Assign(name, e)]
        if is_seq(ty):
            if isinstance(d.type, c_ast.ArrayDecl):
                inner = d.type.type
                if isinstance(inner, c_ast.ArrayDecl):
                    n1 = self.array_len(d.type); n2 = self.array_len(inner)
                    return [Assign(name, SeqLit(n1, ('seqlit', n2, ty[1][1]), ty))]
                return [Assign(name, SeqLit(self.array_len(d.type), ty[1], ty))]
            return [Havoc(name)]
        return [Havoc(name)]

    def lower_init(self, init, ty, env, tnode):
        if isinstance(init, c_ast.InitList):
            if not is_seq(ty):
                raise Unsupported('init list for scalar')
            pre = []
            n = len(init.exprs)
            try:
                n = max(n, self.array_len(tnode))
            except Unsupported:
                pass
            e = SeqLit(n, ty[1], ty)
            for i, x in enumerate(init.exprs):
                p, v = self.lower_expr(x, env)
                pre += p
                e = Upd(e, Const(i, INT), coerce(v, ty[1]), ty)
            return pre, e
        pre, e = self.lower_expr(init, env)
        return pre, coerce(e, ty)

    # ------------------------------------------------------------------ expressions
    def lookup(self, name, env):
        if name in env:
            return env[name]
        raise Unsupported('unknown identifier ' + name)

    def lower_lvalue(self, node, env):
        """Returns (pre, base_var_name, base_ty, path) where path is list of index exprs."""
        if isinstance(node, c_ast.ID):
            k = self.lookup(node.name, env)
            if k[0] == 'alias':
                return [], k[1], k[2], list(k[3])
            return [], k[1], k[2], []
        if isinstance(node, c_ast.ArrayRef):
            pre, base, bty, path = self.lower_lvalue(node.name, env)
            p2, i = self.lower_expr(node.subscript, env)
            return pre + p2, base, bty, path + [coerce(i, INT)]
        if isinstance(node, c_ast.UnaryOp) and node.op == '*':
            pre, base, bty, path = self.lower_lvalue(node.expr, env)
            if is_seq(self.ty_at(bty, path)):
                return pre, base, bty, path + [Const(0, INT)]
            return pre, base, bty, path
        raise Unsupported('lvalue ' + type(node).__name__)

    def ty_at(self, ty, path):
        for _ in path:
            if not is_seq(ty):
                raise Unsupported('index into scalar')
            ty = ty[1]
        return ty

    def read_path(self, base, bty, path):
        e = Var(base, bty)
        t = bty
        for i in path:
            t = t[1]
            e = Idx(e, i, t)
        return e

    def write_path(self, base, bty, path, val):
        """Build base := base[path := val]."""
        def build(cur, t, idxs):
            if not idxs:
                return val
            inner = Idx(cur, idxs[0], t[1])
            return Upd(cur, idxs[0], build(inner, t[1], idxs[1:]), t)
        return Assign(base, build(Var(base, bty), bty, path))

    def lower_expr(self, n, env, discard=False):
        """returns (pre_stmts, expr)"""
        if isinstance(n, c_ast.Constant):
            return [], self.lower_const(n)
        if isinstance(n, c_ast.ID):
            if n.name in ('true', 'false') and n.name not in env:
                return [], Const(n.name == 'true', BOOL)
            if n.name == 'NULL':
                return [], Const(0, INT)
            k = self.lookup(n.name, env)
            if k[0] == 'alias':
                return [], self.read_path(k[1], k[2], k[3])
            return [], Var(k[1], k[2])
        if isinstance(n, c_ast.ArrayRef) or (isinstance(n, c_ast.UnaryOp) and n.op == '*'):
            pre, base, bty, path = self.lower_lvalue(n, env)
            return pre, self.read_path(base, bty, path)
        if isinstance(n, c_ast.Assignment):
            pre, base, bty, path = self.lower_lvalue(n.lvalue, env)
            p2, rhs = self.lower_expr(n.rvalue, env)
            tty = self.ty_at(bty, path)
            cur = self.read_path(base, bty, path)
            if n.op != '=':
                rhs = self.arith(n.op[:-1], cur, rhs)
            rhs = coerce(rhs, tty)
            st = Assign(base, rhs) if not path else self.write_path(base, bty, path, rhs)
            return pre + p2 + [st], self.read_path(base, bty, path)
        if isinstance(n, c_ast.UnaryOp):
            return self.lower_unary(n, env, discard)
        if isinstance(n, c_ast.BinaryOp):
            if n.op in ('&&', '||'):
                pl, l = self.lower_expr(n.left, env)
                pr, r = self.lower_expr(n.right, env)
                l = coerce(l, BOOL); r = coerce(r, BOOL)
                if pr:
                    t = self.declare(self.fresh('sc'), BOOL, env)
                    if n.op == '&&':
                        st = [Assign(t, l), If(Var(t, BOOL), pr + [Assign(t, r)], [])]
                    else:
                        st = [Assign(t, l), If(mk_not(Var(t, BOOL)), pr + [Assign(t, r)], [])]
                    return pl + st, Var(t, BOOL)
                return pl, Bin(n.op, l, r, BOOL)
            pl, l = self.lower_expr(n.left, env)
            pr, r = self.lower_expr(n.right, env)
            return pl + pr, self.arith(n.op, l, r)
        if isinstance(n, c_ast.TernaryOp):
            pc, c = self.lower_expr(n.cond, env)
            pa, a = self.lower_expr(n.iftrue, env)
            pb, b = self.lower_expr(n.iffalse, env)
            ty = arith_ty(a.ty, b.ty) if a.ty in (INT, REAL) and b.ty in (INT, REAL) else a.ty
            a = coerce(a, ty); b = coerce(b, ty)
            if pa or pb:
                t = self.declare(self.fresh('tern'), ty, env)
                return pc + [If(coerce(c, BOOL), pa + [Assign(t, a)], pb + [Assign(t, b)])], Var(t, ty)
            return pc, Ite(coerce(c, BOOL), a, b, ty)
        if isinstance(n, c_ast.Cast):
            pre, e = self.lower_expr(n.expr, env)
            ty = c_type(n.to_type)
            if ty is None:
                return pre, e
            return pre, coerce(e, ty)
        if isinstance(n, c_ast.FuncCall):
            return self.lower_call(n, env, discard)
        if isinstance(n, c_ast.ExprList):
            pre = []
            e = None
            for x in n.exprs:
                p, e = self.lower_expr(x, env)
                pre += p
            return pre, e
        raise Unsupported('expr ' + type(n).__name__)

    def lower_const(self, n):
        v = n.value
        if n.type in ('int', 'long', 'unsigned int', 'long int', 'unsigned long', 'long long'):
            return Const(int(v.rstrip('uUlL'), 0) if not re.match(r'^0[0-7]+$', v.rstrip('uUlL')) else int(v.rstrip('uUlL'), 8), INT)
        if n.type in ('double', 'float', 'long double'):
            return Const(float(v.rstrip('fFlL')), REAL)
        if n.type == 'char':
            s = v[1:-1]
            return Const(ord(s.encode().decode('unicode_escape')), INT)
        if n.type == 'string':
            return Const(0, INT)
        raise Unsupported('const ' + n.type)

    def arith(self, op, l, r):
        if op in ('+', '-', '*', '/'):
            if is_seq(l.ty) or is_seq(r.ty):
                raise Unsupported('pointer arithmetic')
            ty = arith_ty(l.ty if l.ty != BOOL else INT, r.ty if r.ty != BOOL else INT)
            return Bin(op, coerce(l, ty), coerce(r, ty), ty)
        if op == '%':
            return Bin('%', coerce(l, INT), coerce(r, INT), INT)
        if op in ('<', '<=', '>', '>=', '==', '!='):
            if l.ty == BOOL and r.ty == BOOL and op in ('==', '!='):
                return Bin(op, l, r, BOOL)
            ty = arith_ty(l.ty if l.ty != BOOL else INT, r.ty if r.ty != BOOL else INT)
            return Bin(op, coerce(l, ty), coerce(r, ty), BOOL)
        if op in ('&', '|', '^', '<<', '>>'):
            name = {'&': 'band', '|': 'bor', '^': 'bxor', '<<': 'shl', '>>': 'shr'}[op]
            self.externs[name] = ([INT, INT], INT)
            return Call(name, [coerce(l, INT), coerce(r, INT)], INT)
        raise Unsupported('binop ' + op)

    def lower_unary(self, n, env, discard):
        op = n.op
        if op in ('p++', 'p--', '++', '--'):
            pre, base, bty, path = self.lower_lvalue(n.expr, env)
            cur = self.read_path(base, bty, path)
            tty = self.ty_at(bty, path)
            one = Const(1, INT) if tty == INT else Const(1.0, REAL)
            new = Bin('+' if '+' in op else '-', cur, one, tty)
            if op.startswith('p') and not discard:
                t = self.declare(self.fresh('old'), tty, env)
                st = [Assign(t, cur)]
                st.append(Assign(base, new) if not path else self.write_path(base, bty, path, new))
                return pre + st, Var(t, tty)
            st = Assign(base, new) if not path else self.write_path(base, bty, path, new)
            return pre + [st], self.read_path(base, bty, path)
        pre, e = self.lower_expr(n.expr, env)
        if op == '-':
            if e.ty == BOOL:
                e = coerce(e, INT)
            if isinstance(e, Const):
                return pre, Const(-e.val, e.ty)
            return pre, Un('neg', e, e.ty)
        if op == '+':
            return pre, e
        if op == '!':
            return pre, mk_not(coerce(e, BOOL))
        if op == '~':
            self.externs['bnot'] = ([INT], INT)
            return pre, Call('bnot', [coerce(e, INT)], INT)
        if op == 'sizeof':
            return pre, Const(8, INT)
        raise Unsupported('unary ' + op)

    def lower_call(self, n, env, discard):
        if not isinstance(n.name, c_ast.ID):
            raise Unsupported('indirect call')
        f = n.name.name
        args = n.args.exprs if n.args is not None else []
        if f == 'assume' and args:
            pre, c = self.lower_expr(args[0], env)
            return pre + [Assume(coerce(c, BOOL))], Const(0, INT)
        if f in self.choice_funcs:
            pre = []
            vals = []
            for a in args:
                p0, v = self.lower_expr(a, env)
                pre += p0
                vals.append(v)
            proto = self.protos.get(f)
            rty = c_type(proto.type.type) if proto is not None else INT
            t = self.declare(self.fresh('ch_' + f), rty, env)
            return pre + [Choose(t, f, vals, rty)], Var(t, rty)
        if f in IGNORED_CALLS:
            pre = []
            for a in args:
                if isinstance(a, c_ast.Constant) and a.type == 'string':
                    continue
                p, _ = self.lower_expr(a, env)
                pre += p
            return pre, Const(0, INT)
        if f in self.funcs:
            return self.inline_call(f, args, env)
        pre = []
        vals = []
        for a in args:
            p, v = self.lower_expr(a, env)
            pre += p
            vals.append(v)
        if f == 'fabs':
            x = coerce(vals[0], REAL)
            return pre, Ite(Bin('<', x, Const(0.0, REAL), BOOL), Un('neg', x, REAL), x, REAL)
        if f in ('abs', 'labs'):
            x = coerce(vals[0], INT)
            return pre, Ite(Bin('<', x, Const(0, INT), BOOL), Un('neg', x, INT), x, INT)
        if f in ('fmax', 'fmin'):
            a, b = coerce(vals[0], REAL), coerce(vals[1], REAL)
            return pre, Ite(Bin('>' if f == 'fmax' else '<', a, b, BOOL), a, b, REAL)
        if f in MATH_REAL1:
            self.externs[f] = ([REAL], REAL)
            return pre, Call(f, [coerce(vals[0], REAL)], REAL)
        if f in MATH_REAL2:
            self.externs[f] = ([REAL, REAL], REAL)
            return pre, Call(f, [coerce(v, REAL) for v in vals], REAL)
        if f in self.protos:
            proto = self.protos[f]
            rty = c_type(proto.type.type)
            ptys = [c_type(p.type) for p in (proto.type.args.params if proto.type.args else [])
                    if not (isinstance(p, c_ast.Typename) and c_type(p.type) is None)]
            self.externs[f] = (ptys, rty)
            return pre, Call(f, [coerce(v, t) for v, t in zip(vals, ptys)], rty)
        raise Unsupported('unknown function ' + f)

    def inline_call(self, f, args, env):
        fd = self.funcs[f]
        rty = c_type(fd.decl.type.type)
        params = self.param_decls(fd)
        if len(params) != len(args):
            raise Unsupported('arity')
        pre = []
        vals = []
        for a, p in zip(args, params):
            pty = c_type(p.type)
            if is_seq(pty):
                # pass by alias
                if isinstance(a, c_ast.UnaryOp) and a.op == '&':
                    p0, base, bty, path = self.lower_lvalue(a.expr, env)
                    pre += p0
                    vals.append(('alias', base, bty, path, True))
                else:
                    p0, base, bty, path = self.lower_lvalue(a, env)
                    pre += p0
                    vals.append(('alias', base, bty, path, False))
            else:
                p0, v = self.lower_expr(a, env)
                pre += p0
                vals.append(('val', coerce(v, pty)))
        if f in self.call_stack:
            # recursive call: abstract with an uninterpreted function (mutual summary)
            if any(v[0] == 'alias' for v in vals):
                raise Unsupported('recursive call with pointer args')
            name = 'rec_' + f
            ptys = [c_type(p.type) for p in params]
            self.externs[name] = (ptys, rty)
            self.recursive_used.add(f)
            return pre, Call(name, [v[1] for v in vals], rty)
        if len(self.call_stack) > 30:
            raise Unsupported('inline depth')
        env2 = {}
        for (gname, gty, _, _) in self.globals:
            env2[gname] = ('var', gname, gty)
        body_pre = []
        for v, p in zip(vals, params):
            pty = c_type(p.type)
            if v[0] == 'alias':
                _, base, bty, path, addr = v
                if addr:
                    # &x passed for pointer param: *p and p[0] both mean x(path)
                    tgt_ty = self.ty_at(bty, path)
                    if is_seq(tgt_ty):
                        env2[p.name] = ('alias', base, bty, path)
                    else:
                        env2[p.name] = ('alias_scalar', base, bty, path)
                else:
                    env2[p.name] = ('alias', base, bty, path)
            else:
                nm = self.declare(p.name, pty, env2)
                body_pre.append(Assign(nm, v[1]))
        # scalar alias: represent pointer to scalar as a 'path' alias, *p resolves to the var itself
        for k, v in list(env2.items()):
            if v[0] == 'alias_scalar':
                env2[k] = ('ptr_scalar', v[1], v[2], v[3])
        retvar = None
        if rty is not None:
            retvar = self.declare(self.fresh(f + '_ret'), rty, {})
        self.call_stack.append(f)
        saved = getattr(self, 'loop_flags', [])
        self._env_hook = env2
        raw = self.lower_stmt(fd.body, env2, retvar, rty)
        body = eliminate_jumps(raw, retvar, self)
        self.loop_flags = saved
        self.call_stack.pop()
        out = pre + body_pre + body
        if rty is None:
            return out, Const(0, INT)
        return out, Var(retvar, rty)


# patch lookup to support pointer-to-scalar aliases transparently
_orig_lower_lvalue = Frontend.lower_lvalue


def _lower_lvalue(self, node, env):
    if isinstance(node, c_ast.UnaryOp) and node.op == '*' and isinstance(node.expr, c_ast.ID):
        k = env.get(node.expr.name)
        if k and k[0] == 'ptr_scalar':
            return [], k[1], k[2], list(k[3])
    if isinstance(node, c_ast.ArrayRef) and isinstance(node.name, c_ast.ID):
        k = env.get(node.name.name)
        if k and k[0] == 'ptr_scalar':
            return [], k[1], k[2], list(k[3])  # p[0]
    return _orig_lower_lvalue(self, node, env)


Frontend.lower_lvalue = _lower_lvalue


class _Loop(Stmt):
    """Loop before jump elimination."""

    def __init__(self, c, cpre, body, nxt, is_do):
        self.c, self.cpre, self.body, self.nxt, self.is_do = c, cpre, body, nxt, is_do
        self.ghost = False


# ---------------------------------------------------------------------- jump elimination
def _has(ss, kinds, into_loops):
    for s in ss:
        if isinstance(s, kinds):
            return True
        if isinstance(s, If) and (_has(s.th, kinds, into_loops) or _has(s.el, kinds, into_loops)):
            return True
        if isinstance(s, _Loop) and into_loops and _has(s.body, kinds, into_loops):
            return True
    return False


def _always_returns(ss):
    for s in ss:
        if isinstance(s, _Ret):
            return True
        if isinstance(s, If) and _always_returns(s.th) and _always_returns(s.el):
            return True
        if isinstance(s, (_Brk, _Cont)):
            return False
    return False


def eliminate_jumps(ss, retvar, fe):
    ctx = {'ret': None}

    def retflag():
        if ctx['ret'] is None:
            nm = fe.fresh('returned')
            fe.locals[nm] = BOOL
            ctx['ret'] = nm
        return ctx['ret']

    def seq(ss, loop):
        """loop: dict with 'brk','cont' flag names (lazily created) or None."""
        out = []
        for i, s in enumerate(ss):
            rest = ss[i + 1:]
            if isinstance(s, _Ret):
                if s.e is not None and retvar is not None:
                    out.append(Assign(retvar, s.e))
                if loop is not None or _need_flag['ret']:
                    out.append(Assign(retflag(), TRUE))
                return out
            if isinstance(s, _Brk):
                out.append(Assign(loop_flag(loop, 'brk'), TRUE))
                return out
            if isinstance(s, _Cont):
                out.append(Assign(loop_flag(loop, 'cont'), TRUE))
                return out
            if isinstance(s, If) and loop is None and not _need_flag['ret']:
                th_r, el_r = _always_returns(s.th), _always_returns(s.el)
                if (th_r or el_r) and not _has(s.th + s.el, (_Brk, _Cont), False) and \
                        not _ret_in_loop(s.th + s.el):
                    th = s.th if th_r else s.th + rest
                    el = s.el if el_r else s.el + rest
                    out.append(If(s.c, seq(th, loop), seq(el, loop)))
                    return out
            if isinstance(s, If):
                jumps = _has(s.th + s.el, (_Ret, _Brk, _Cont), False) or _ret_in_loop(s.th + s.el)
                out.append(If(s.c, seq(s.th, loop), seq(s.el, loop)))
                if jumps and rest:
                    out.append(If(mk_not(any_flag(loop, s.th + s.el)), seq(rest, loop), []))
                    return out
                continue
            if isinstance(s, _Loop):
                out += lower_loop(s, loop)
                if _ret_in_loop([s]) and rest:
                    out.append(If(mk_not(Var(retflag(), BOOL)), seq(rest, loop), []))
                    return out
                continue
            out.append(s)
        return out

    def loop_flag(loop, k):
        if loop[k] is None:
            nm = fe.fresh(k)
            fe.locals[nm] = BOOL
            loop[k] = nm
        return loop[k]

    def any_flag(loop, body):
        e = FALSE
        if _has(body, (_Ret,), False) or _ret_in_loop(body):
            e = mk_or(e, Var(retflag(), BOOL))
        if loop is not None:
            if _has(body, (_Brk,), False):
                e = mk_or(e, Var(loop_flag(loop, 'brk'), BOOL))
            if _has(body, (_Cont,), False):
                e = mk_or(e, Var(loop_flag(loop, 'cont'), BOOL))
        return e

    def lower_loop(lp, outer):
        loop = {'brk': None, 'cont': None}
        body = seq(lp.body, loop)
        has_ret = _ret_in_loop([lp])
        stmts = []
        if loop['cont'] is not None:
            body = [Assign(loop['cont'], FALSE)] + body
        flags = TRUE
        if loop['brk'] is not None:
            stmts.append(Assign(loop['brk'], FALSE))
            flags = mk_not(Var(loop['brk'], BOOL))
        if has_ret:
            flags = mk_and(flags, mk_not(Var(retflag(), BOOL)))
        if lp.cpre:
            t = fe.fresh('lc')
            fe.locals[t] = BOOL
            guard_pre = lp.cpre + [Assign(t, lp.c)]
            ctest = Var(t, BOOL)
        else:
            guard_pre = []
            ctest = lp.c
        tail = list(lp.nxt) + guard_pre
        if tail:
            if isinstance(flags, Const):
                body = body + tail
            else:
                body = body + [If(flags, tail, [])]
        if lp.is_do:
            first = fe.fresh('first')
            fe.locals[first] = BOOL
            stmts.append(Assign(first, TRUE))
            if lp.cpre:
                stmts.append(Assign(ctest.name, FALSE))
            ctest = mk_or(Var(first, BOOL), ctest)
            body = [Assign(first, FALSE)] + body
        else:
            stmts += guard_pre
        stmts.append(While(mk_and(flags, ctest), body))
        return stmts

    _need_flag = {'ret': _ret_in_loop(ss)}
    if _need_flag['ret']:
        retflag()
        out = [Assign(ctx['ret'], FALSE)] + seq(ss, None)
    else:
        out = seq(ss, None)
    return out


def _strip_extra(cond, c):
    """cond is (flags && c); return the flags part."""
    if isinstance(cond, Bin) and cond.op == '&&':
        if cond.r is c:
            return cond.l
        return mk_and(_strip_extra(cond.l, c), cond.r) if cond.r is not c else cond.l
    return TRUE


def _ret_in_loop(ss):
    for s in ss:
        if isinstance(s, _Loop) and _has(s.body, (_Ret,), True):
            return True
        if isinstance(s, If) and _ret_in_loop(s.th + s.el):
            return True
    return False


def load_program(path_or_src, entry, is_src=False, tag='', with_rec=True, choice_funcs=()) -> Program:
    """Lower `entry`.  Recursive functions f reached from it appear as calls to the uninterpreted
    function rec_f; their own (lowered) bodies are returned in prog.rec_funcs[f] so they can be
    executed concretely and related by a separate mutual-summary obligation."""
    src = path_or_src if is_src else open(path_or_src).read()
    fe = Frontend(src, tag, choice_funcs)
    prog = fe.lower_entry(entry, global_inputs=True)
    prog.recursive = sorted(fe.recursive_used)
    prog.frontend = fe
    prog.src = src
    prog.rec_funcs = {}
    if with_rec:
        todo = list(prog.recursive)
        while todo:
            f = todo.pop()
            if f in prog.rec_funcs:
                continue
            fe2 = Frontend(src, tag)
            sub = fe2.lower_entry(f, global_inputs=False)
            prog.rec_funcs[f] = sub
            for g in fe2.recursive_used:
                if g not in prog.rec_funcs:
                    todo.append(g)
    return prog
