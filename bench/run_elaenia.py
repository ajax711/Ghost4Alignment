"""Forall-exists benchmarks from the KestRel/Elaenia suite (benchmarks/elaenia, 37 programs:
GNI from Unno et al., refinement examples, Antonopoulos et al. ForEx examples, Barthe et al.).

usage: python3 bench/run_elaenia.py <kestrel/benchmarks/elaenia> <out.jsonl> [--jobs 4]
"""
import argparse, json, os, re, sys, time, traceback, random, multiprocessing as mp
sys.path.insert(0, os.path.join(os.path.dirname(__file__), '..'))


def parse_header(src):
    m = re.search(r'/\*\s*@ELAENIA(.*?)\*/', src, re.S)
    body = re.sub(r'^\s*\*', ' ', m.group(1), flags=re.M)
    out = {}
    ia = body.find('aspecs:')
    ie = body.find('especs:')
    head = body[:min(x for x in (ia, ie, len(body)) if x >= 0)]
    out['aspecs'] = body[ia + 7:(ie if ie > ia else len(body))] if ia >= 0 else ''
    out['especs'] = body[ie + 7:(ia if ia > ie else len(body))] if ie >= 0 else ''
    keys = ['pre', 'forall', 'exists', 'post']
    for k in keys:
        mm = re.search(r'(?<![\w.])' + k + r'\s*:(.*?)(?=(?<![\w.])(' + '|'.join(keys) + r')\s*:|$)', head, re.S)
        out[k] = mm.group(1).strip() if mm else ''
    for k in ('pre', 'post', 'forall', 'exists'):
        out[k] = ' '.join(out[k].split()).rstrip(';').strip()
    return out


def map_names(cond, where):
    if where == 'pre':
        cond = re.sub(r'\bforall\.(\w+)', r'in_l_\1', cond)
        cond = re.sub(r'\bexists\.(\w+)', r'in_r_\1', cond)
    else:
        cond = re.sub(r'\bforall\.(\w+)', r'l_\1', cond)
        cond = re.sub(r'\bexists\.(\w+)', r'r_\1', cond)
    return cond


def work(args):
    path, budget = args
    from ghostweave.cfront import load_program, Unsupported
    from ghostweave.forall_exists import AEProblem, parse_specs, verify_ae, cond_to_py
    from ghostweave.driver import gen_inputs
    rec = {'bench': os.path.relpath(path, os.path.dirname(os.path.dirname(path)))}
    t0 = time.time()
    try:
        src = open(path).read()
        hd = parse_header(src)
        aspecs = parse_specs(hd['aspecs'])
        especs = parse_specs(hd['especs'])
        choice = set(aspecs) | set(especs)
        # the `_f` implementations are only for KestRel's test generation; drop them
        pA = load_program(src, hd['forall'], is_src=True, choice_funcs=choice)
        pE = load_program(src, hd['exists'], is_src=True, choice_funcs=choice)
        pre = map_names(hd['pre'] or 'true', 'pre')
        post = map_names(hd['post'], 'post')
        prob = AEProblem(pA, pE, pre, post, aspecs, especs)
        # inputs: honour equalities of the precondition, filter by its python reading
        eqs = re.findall(r'forall\.(\w+)\s*==\s*exists\.(\w+)', hd['pre'])
        pyt = cond_to_py(pre)
        rng = random.Random(7)
        inputs = []
        for _ in range(2000):
            d = {}
            for n, t in pA.func.params:
                d['in_l_' + n] = gen_inputs([(n, t)], 1, rng.randint(0, 10**9))[0][n]
            for n, t in pE.func.params:
                d['in_r_' + n] = gen_inputs([(n, t)], 1, rng.randint(0, 10**9))[0][n]
            for a, b in eqs:
                if 'in_l_' + a in d and 'in_r_' + b in d:
                    d['in_r_' + b] = d['in_l_' + a]
            if pyt is not None:
                try:
                    if not eval(pyt, {}, dict(d)):
                        continue
                except Exception:
                    continue
            inputs.append(d)
            if len(inputs) >= 30:
                break
        rec['n_inputs'] = len(inputs)
        verdict, info = verify_ae(prob, inputs, time_budget=budget)
        rec.update(verdict=verdict, plan=info.get('plan'), witness=info.get('witness'),
                   tried=info.get('tried'), dafny=info.get('dafny'), viable=info.get('viable'))
    except Unsupported as e:
        rec['verdict'] = 'unsupported'; rec['reason'] = str(e)
    except Exception as e:
        rec['verdict'] = 'crash'; rec['reason'] = type(e).__name__ + ': ' + str(e)[:300]
        rec['trace'] = traceback.format_exc()[-2000:]
    rec['time'] = round(time.time() - t0, 2)
    return rec


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('root'); ap.add_argument('out')
    ap.add_argument('--jobs', type=int, default=4)
    ap.add_argument('--budget', type=float, default=240)
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
            print(f"{rec['bench']:42s} {rec['verdict']:12s} {rec['time']:7.1f}s {rec.get('plan') or rec.get('reason','')} {rec.get('witness') or ''}", flush=True)


if __name__ == '__main__':
    main()
