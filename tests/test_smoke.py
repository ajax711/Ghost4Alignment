"""Smoke tests: python3 -m pytest -q tests   (needs `dafny` on PATH)"""
import os, sys
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))
from ghostweave.cfront import load_program
from ghostweave.driver import Problem, verify, differential_test
from ghostweave.ir import While, If, Assign

HERE = os.path.dirname(__file__)
EX = os.path.join(HERE, '..', 'examples', 'eq', 'barthe.c')


def ghost_projection(ss):
    """statements with ghost flag, structure preserved (used to check the weaving's P2 projection)"""
    out = []
    for s in ss:
        if isinstance(s, If):
            out += ghost_projection(s.th) + ghost_projection(s.el)
        elif isinstance(s, While):
            out += ghost_projection(s.body)
        elif s.ghost:
            out.append(s)
    return out


def test_proves_barthe():
    p1 = load_program(EX, 'old_f')
    p2 = load_program(EX, 'new_f')
    assert differential_test(p1, p2) is None
    verdict, info = verify(Problem(p1, p2), time_budget=200)
    assert verdict == 'proved', info


def test_refutes_mutant():
    src = open(EX).read().replace('j = j + 5;', 'j = j + 4;')
    p1 = load_program(src, 'old_f', is_src=True)
    p2 = load_program(src, 'new_f', is_src=True)
    assert differential_test(p1, p2) is not None
    verdict, _ = verify(Problem(p1, p2), time_budget=60, top_k=2)
    assert verdict != 'proved'


def test_real_code_is_untouched():
    """erasure: dropping ghost statements from any weaving gives back P1's statements"""
    from ghostweave.driver import seq_plans
    p1 = load_program(EX, 'old_f')
    p2 = load_program(EX, 'new_f')
    prob = Problem(p1, p2)

    def real(ss):
        out = []
        for s in ss:
            if s.ghost:
                continue
            if isinstance(s, While):
                out.append(('while', repr(s.c), tuple(real(s.body))))
            elif isinstance(s, If):
                out.append(('if', repr(s.c), tuple(real(s.th)), tuple(real(s.el))))
            else:
                out.append(repr(s))
        return out
    ref = None
    for plan in seq_plans(prob.A, prob.B):
        w = prob.weave(plan)
        r = real(w['body'])
        ref = ref or r
        assert r == ref, plan.describe()
