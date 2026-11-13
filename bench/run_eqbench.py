"""Run GhostWeave on every EqBench pair that has a C-Desc.json (135 Eq + 113 Neq = 248 pairs).

usage: python3 bench/run_eqbench.py <EqBench/benchmarks dir> <out.jsonl> [--jobs 4] [--filter substr]
"""
import argparse, json, os, sys, time, traceback, multiprocessing as mp
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))


def pairs(root):
    for d, dirs, files in sorted(os.walk(root)):
        if os.path.basename(d) in ('Eq', 'Neq') and os.path.exists(os.path.join(d, 'C-Desc.json')):
            yield d


def work(args):
    d, root, budget = args
    from ghostweave.cfront import load_program, Unsupported
    from ghostweave.driver import Problem, verify, differential_test, prove_recursive
    rel = os.path.relpath(d, root)
    rec = {'pair': rel, 'label': os.path.basename(d)}
    t0 = time.time()
    try:
        desc = json.load(open(os.path.join(d, 'C-Desc.json')))
        rec['loops'] = desc.get('# Loops')
        fn = desc['function name']
        fs = os.listdir(d)
        o = [f for f in fs if f.startswith('old') and f.endswith('.c')][0]
        n = [f for f in fs if f.startswith('new') and f.endswith('.c')][0]
        # CLEVER pairs are client-specific: equivalence is claimed for the client `main`
        if str(desc.get('program name', '')).endswith('.main') and 'main(' in open(os.path.join(d, o)).read():
            fn = 'main'
        rec['entry'] = fn
        p1 = load_program(os.path.join(d, o), fn)
        p2 = load_program(os.path.join(d, n), fn)
        rec['recursive'] = sorted(set(p1.recursive) | set(p2.recursive))
        w = differential_test(p1, p2)
        rec['witness'] = None if w is None else {k: repr(v) for k, v in w.items()}
        shared, rdet = prove_recursive(p1, p2, time_budget=budget / 2)
        rec['rec_shared'] = sorted(shared)
        rec['rec_details'] = rdet
        prob = Problem(p1, p2, shared=shared)
        verdict, info = verify(prob, time_budget=budget)
        rec['verdict'] = verdict
        rec['plan'] = info.get('plan')
        rec['plans_total'] = info.get('plans_total')
        rec['plans_viable'] = info.get('plans_viable')
        rec['tried'] = info.get('tried')
        rec['dafny'] = info.get('dafny')
    except Unsupported as e:
        rec['verdict'] = 'unsupported'
        rec['reason'] = str(e)
    except Exception as e:
        rec['verdict'] = 'crash'
        rec['reason'] = type(e).__name__ + ': ' + str(e)[:300]
        rec['trace'] = traceback.format_exc()[-1500:]
    rec['time'] = round(time.time() - t0, 2)
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('root'); ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--filter', default='')
    ap.add_argument('--budget', type=float, default=400)
    a = ap.parse_args()
    todo = [(d, a.root, a.budget) for d in pairs(a.root) if a.filter in d]
    with mp.Pool(a.jobs) as pool, open(a.out, 'w') as f:
        for rec in pool.imap_unordered(work, todo):
            f.write(json.dumps(rec) + '\n'); f.flush()
            print(f"{rec['pair']:45s} {rec['verdict']:12s} wit={'Y' if rec.get('witness') else '-'} {rec['time']:7.1f}s {rec.get('plan') or rec.get('reason','')}", flush=True)


if __name__ == '__main__':
    main()
