"""Run GhostWeave on the KestRel benchmark suite (benchmarks/euf: 31 programs from Barthe et al.,
Antonopoulos et al., Sousa & Dillig, Unno et al., Churchill et al., plus ADT examples).

The `_invariant(...)` hints that KestRel's inputs carry are ignored: GhostWeave infers all
invariants.  Relational pre/postconditions are taken verbatim from the @KESTREL header.

usage: python3 bench/run_kestrel.py <kestrel/benchmarks/euf> <out.jsonl> [--jobs 4]
"""
import argparse, json, os, re, sys, time, traceback, random, hashlib, multiprocessing as mp
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))


def parse_header(src):
    m = re.search(r'/\*\s*@KESTREL(.*?)\*/', src, re.S)
    body = re.sub(r'^\s*\*', ' ', m.group(1), flags=re.M)
    fields = {}
    for key in ('pre', 'left', 'right', 'post'):
        mm = re.search(key + r'\s*:(.*?);(?=\s*(pre|left|right|post)\s*:|\s*$)', body, re.S)
        fields[key] = ' '.join(mm.group(1).split()) if mm else None
    return fields


def to_dafny(cond, lparams, rparams, where):
    """left.x / right.x / l_x / r_x  ->  GhostWeave names.  where: 'pre' (inputs) or 'post' (final state)."""
    def lname(x, side, params):
        if where == 'pre':
            return f'in_{side}_{x}'
        return f'{side}_{x}'
    cond = re.sub(r'\bleft\.(\w+)', lambda m: lname(m.group(1), 'l', lparams), cond)
    cond = re.sub(r'\bright\.(\w+)', lambda m: lname(m.group(1), 'r', rparams), cond)
    if where == 'pre':
        cond = re.sub(r'\b(?<!in_)l_(\w+)', lambda m: f'in_l_{m.group(1)}', cond)
        cond = re.sub(r'\b(?<!in_)r_(\w+)', lambda m: f'in_r_{m.group(1)}', cond)
    return cond


# --- concrete model of the uninterpreted array theory (read/store over integer handles) ----------
class Heap:
    """Arrays are integer handles; equal contents <=> equal handles (so equalities can be mined)."""
    def __init__(self):
        self.ov = {}       # handle -> (base, frozenset overrides)
        self.canon = {}

    def base_val(self, base, i, real):
        h = int(hashlib.md5(f'{base}:{i}'.encode()).hexdigest()[:6], 16)
        return (h % 41 - 20) / 4.0 if real else h % 41 - 20

    def read(self, a, i, real=False):
        base, ovs = self.ov.get(a, (a, frozenset()))
        d = dict(ovs)
        return d[i] if i in d else self.base_val(base, i, real)

    def store(self, a, i, x, real=False):
        base, ovs = self.ov.get(a, (a, frozenset()))
        d = dict(ovs)
        if x == self.base_val(base, i, real):
            d.pop(i, None)
        else:
            d[i] = x
        key = (base, frozenset(d.items()))
        if not d:
            return base
        if key not in self.canon:
            h = 10 ** 9 + len(self.canon)
            self.canon[key] = h
            self.ov[h] = key
        return self.canon[key]


def work(args):
    path, budget = args
    from ghostweave.cfront import load_program, Unsupported
    from ghostweave.driver import Problem, verify, differential_test, prove_recursive
    from ghostweave.ir import Raw, Bin, Var, BOOL
    from ghostweave import interp as I
    rec = {'bench': os.path.relpath(path, os.path.dirname(os.path.dirname(path)))}
    t0 = time.time()
    try:
        src = open(path).read()
        hd = parse_header(src)
        rec['post'] = hd['post']
        p1 = load_program(src, hd['left'], is_src=True)
        p2 = load_program(src, hd['right'], is_src=True)
        lp = [n for n, _ in p1.func.params]
        rp = [n for n, _ in p2.func.params]
        pre_txt = to_dafny(hd['pre'], lp, rp, 'pre') if hd['pre'] else 'true'
        post_txt = to_dafny(hd['post'], lp, rp, 'post')
        heap = Heap()
        real_read = any(f == 'read' and rt == 'real' for f, (_, rt) in p1.externs.items())
        I.EXTERN_IMPL['read'] = lambda a, i: heap.read(a, i, real_read)
        I.EXTERN_IMPL['store'] = lambda a, i, x: heap.store(a, i, x, real_read)
        from ghostweave.forall_exists import py_pred
        prob = Problem(p1, p2, pre=[Raw(pre_txt)], post_obs=[], post_raw=Raw(post_txt, py=py_pred(post_txt)))
        # sampler: honour the simple equalities left.x == right.y of the precondition
        eqs = re.findall(r'left\.(\w+)\s*==\s*right\.(\w+)', hd['pre'] or '')
        bounds = re.findall(r'(-?\d+)\s*<=?\s*left\.(\w+)', hd['pre'] or '')
        def sampler(d, rng):
            for k in list(d):
                if isinstance(d[k], int) and not isinstance(d[k], bool):
                    d[k] = abs(d[k]) % 12
            for a, b in eqs:
                if 'in_l_' + a in d and 'in_r_' + b in d:
                    d['in_r_' + b] = d['in_l_' + a]
            for c, a in bounds:
                if 'in_l_' + a in d and d['in_l_' + a] < int(c):
                    return None
            return d
        prob.custom_pre_sampler = sampler
        verdict, info = verify(prob, time_budget=budget)
        rec['verdict'] = verdict
        rec['plan'] = info.get('plan')
        rec['tried'] = info.get('tried')
        rec['dafny'] = info.get('dafny')
        rec['plans_total'] = info.get('plans_total')
        rec['plans_viable'] = info.get('plans_viable')
    except Unsupported as e:
        rec['verdict'] = 'unsupported'; rec['reason'] = str(e)
    except Exception as e:
        rec['verdict'] = 'crash'; rec['reason'] = type(e).__name__ + ': ' + str(e)[:300]
        rec['trace'] = traceback.format_exc()[-1500:]
    rec['time'] = round(time.time() - t0, 2)
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('root'); ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--budget', type=float, default=300)
    ap.add_argument('--filter', default='')
    a = ap.parse_args()
    todo = []
    for d, _, fs in sorted(os.walk(a.root)):
        for f in sorted(fs):
            if f.endswith('.c') and a.filter in os.path.join(d, f):
                todo.append((os.path.join(d, f), a.budget))
    with mp.Pool(a.jobs) as pool, open(a.out, 'w') as f:
        for rec in pool.imap_unordered(work, todo):
            f.write(json.dumps(rec) + '\n'); f.flush()
            print(f"{rec['bench']:40s} {rec['verdict']:12s} {rec['time']:7.1f}s {rec.get('plan') or rec.get('reason','')}", flush=True)


if __name__ == '__main__':
    main()
