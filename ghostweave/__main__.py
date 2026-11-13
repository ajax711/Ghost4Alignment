"""python3 -m ghostweave OLD.c NEW.c --entry f [--entry2 g] [--show]

Checks equivalence of OLD's f and NEW's g (same name by default): differential testing, then the
automatic ghost weaving search.  With --show, prints the woven Dafny program that verified."""
import argparse
import sys
from .cfront import load_program
from .driver import Problem, verify, differential_test, prove_recursive


def main():
    ap = argparse.ArgumentParser(prog='ghostweave')
    ap.add_argument('old')
    ap.add_argument('new')
    ap.add_argument('--entry', required=True)
    ap.add_argument('--entry2')
    ap.add_argument('--budget', type=float, default=300)
    ap.add_argument('--show', action='store_true')
    ap.add_argument('-v', '--verbose', action='store_true')
    a = ap.parse_args()
    p1 = load_program(a.old, a.entry)
    p2 = load_program(a.new, a.entry2 or a.entry)
    w = differential_test(p1, p2)
    if w is not None:
        print('NOT EQUIVALENT: counterexample', w)
        return 1
    shared, _ = prove_recursive(p1, p2, time_budget=a.budget / 3)
    verdict, info = verify(Problem(p1, p2, shared=shared), time_budget=a.budget, verbose=a.verbose)
    if verdict == 'proved':
        print('EQUIVALENT (verified by Dafny), alignment:', info['plan'])
        if a.show:
            print(info['dafny'])
        return 0
    print('UNKNOWN: no weaving verified within budget')
    for t in info.get('tried', []):
        print('  tried', t['plan'], '->', t['errors'][:2])
    return 2


if __name__ == '__main__':
    sys.exit(main())
