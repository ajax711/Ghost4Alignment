"""Summarize result JSONL files into results/SUMMARY.md"""
import collections, json, os, sys

HERE = os.path.dirname(os.path.abspath(__file__))
RES = os.path.join(HERE, '..', 'results')


def load(name):
    p = os.path.join(RES, name)
    if not os.path.exists(p):
        return []
    return [json.loads(l) for l in open(p)]


def eqbench(rs, out):
    out.append('## EqBench (C, 248 pairs with metadata: 135 Eq / 113 Neq)\n')
    eq = [r for r in rs if r['label'] == 'Eq']
    neq = [r for r in rs if r['label'] == 'Neq']
    def cnt(lst, f):
        return sum(1 for r in lst if f(r))
    out.append('| | Eq pairs | Neq pairs |')
    out.append('|---|---|---|')
    out.append(f'| total run | {len(eq)} | {len(neq)} |')
    out.append(f'| **proved equivalent** (Dafny) | **{cnt(eq, lambda r: r["verdict"] == "proved")}** | {cnt(neq, lambda r: r["verdict"] == "proved")} |')
    out.append(f'| refuted (concrete counterexample) | {cnt(eq, lambda r: r.get("witness"))} | **{cnt(neq, lambda r: r.get("witness"))}** |')
    out.append(f'| unknown | {cnt(eq, lambda r: r["verdict"] == "unknown" and not r.get("witness"))} | {cnt(neq, lambda r: r["verdict"] == "unknown" and not r.get("witness"))} |')
    out.append(f'| unsupported C (frontend) | {cnt(eq, lambda r: r["verdict"] == "unsupported")} | {cnt(neq, lambda r: r["verdict"] == "unsupported")} |')
    out.append(f'| crash | {cnt(eq, lambda r: r["verdict"] == "crash")} | {cnt(neq, lambda r: r["verdict"] == "crash")} |')
    out.append('')
    bad = [r['pair'] for r in neq if r['verdict'] == 'proved']
    out.append(f'Neq pairs proved equivalent (would indicate unsoundness or a semantic gap): **{len(bad)}** {bad if bad else ""}\n')
    wit_eq = [r for r in eq if r.get('witness')]
    if wit_eq:
        out.append('Eq-labeled pairs for which the differential tester found a counterexample '
                   '(either a mislabeled pair or a gap between our idealized semantics and C):\n')
        for r in wit_eq:
            out.append(f'* `{r["pair"]}`: {r["witness"]}')
        out.append('')
    # by benchmark family
    fam = collections.defaultdict(lambda: collections.Counter())
    for r in rs:
        b = r['pair'].split('/')[0]
        fam[b][(r['label'], 'proved' if r['verdict'] == 'proved' else ('refuted' if r.get('witness') else r['verdict']))] += 1
        fam[b][(r['label'], 'n')] += 1
    out.append('| family | Eq proved / Eq | Neq refuted / Neq | Eq unsupported |')
    out.append('|---|---|---|---|')
    for b in sorted(fam):
        c = fam[b]
        out.append(f'| {b} | {c[("Eq","proved")]}/{c[("Eq","n")]} | {c[("Neq","refuted")]}/{c[("Neq","n")]} | {c[("Eq","unsupported")]} |')
    out.append('')
    # loops vs loop-free
    lp = [r for r in eq if (r.get('loops') or 0) > 0]
    nl = [r for r in eq if not (r.get('loops') or 0)]
    out.append(f'Eq pairs with loops: {cnt(lp, lambda r: r["verdict"] == "proved")}/{len(lp)} proved; '
               f'loop-free: {cnt(nl, lambda r: r["verdict"] == "proved")}/{len(nl)} proved.\n')
    plans = collections.Counter()
    for r in eq:
        if r['verdict'] == 'proved':
            p = r.get('plan') or ''
            kind = 'sequential (no loop pair matched)' if p == 'sequential' else (
                'nested' if 'nested' in p else ('lag/peel' if ('lag' in p or 'peel' in p) else (
                    'n:m' if ('steps' in p or 'every' in p) else ('if-structured' if 'if[' in p else 'lockstep'))))
            plans[kind] += 1
    out.append('Alignment used by proved Eq pairs: ' + ', '.join(f'{k}: {v}' for k, v in plans.most_common()) + '\n')
    times = sorted(r['time'] for r in eq if r['verdict'] == 'proved')
    if times:
        out.append(f'Time to proof (Eq): median {times[len(times)//2]:.1f}s, max {times[-1]:.1f}s '
                   '(4-core VM, several suites running concurrently).\n')
    unk = [r for r in eq if r['verdict'] in ('unknown',) and not r.get('witness')]
    if unk:
        out.append('<details><summary>Eq pairs not proved</summary>\n')
        for r in sorted(unk, key=lambda r: r['pair']):
            t = (r.get('tried') or [{}])[0]
            out.append(f'* `{r["pair"]}` loops={r.get("loops")} rec={r.get("rec_shared")}/{r.get("recursive")} '
                       f'first error: {(t.get("errors") or [""])[:1]}')
        out.append('\n</details>\n')
    uns = collections.Counter(r.get('reason', '')[:40] for r in rs if r['verdict'] == 'unsupported')
    out.append('Unsupported reasons: ' + ', '.join(f'{k} ({v})' for k, v in uns.most_common()) + '\n')


def kestrel(rs, out, title, key='bench'):
    out.append(f'## {title}\n')
    c = collections.Counter(r['verdict'] for r in rs)
    out.append(f'{c["proved"]}/{len(rs)} proved; ' + ', '.join(f'{k}: {v}' for k, v in c.items() if k != 'proved') + '\n')
    out.append('| benchmark | verdict | time (s) | alignment | witnesses |')
    out.append('|---|---|---|---|---|')
    for r in sorted(rs, key=lambda r: r[key]):
        out.append(f'| {r[key]} | {r["verdict"]} | {r["time"]} | {r.get("plan") or r.get("reason","") or ""} | {r.get("witness") or ""} |')
    out.append('')


def main():
    out = ['# GhostWeave results\n',
           'Generated by `bench/summarize.py` from the JSONL files in this directory. '
           'Every "proved" record contains the exact Dafny file that the stock verifier accepted.\n']
    rs = load(sys.argv[1] if len(sys.argv) > 1 else 'eqbench_v2.jsonl')
    if rs:
        eqbench(rs, out)
    k = load('kestrel_euf_v1.jsonl')
    if k:
        kestrel(k, out, 'KestRel `euf` suite (forall-forall; KestRel\'s `_invariant` hints ignored)')
    e = load('elaenia_v1.jsonl')
    if e:
        kestrel(e, out, 'Elaenia suite (forall-exists)')
    p = load('prophecy.jsonl')
    if p:
        kestrel(p, out, 'Prophecy examples (examples/prophecy)')
    pn = load('prophecy_noprophecy.jsonl')
    if pn:
        kestrel(pn, out, 'Prophecy examples with prophecy disabled (ablation)')
    open(os.path.join(RES, 'SUMMARY.md'), 'w').write('\n'.join(out) + '\n')
    print('\n'.join(out))


if __name__ == '__main__':
    main()
