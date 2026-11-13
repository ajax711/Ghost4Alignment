# GhostWeave: relational verification as ghost code

GhostWeave proves relational properties of two programs (equivalence, refinement, generalized
non-interference) **without building a product program**.  It weaves program P2 into program P1 as
*ghost code* and hands the result, a single ordinary method, to the **stock Dafny verifier**.

```
P1 (real)     ──┐                         ┌──────────────────────────────┐
                ├─ weave (placement = ───▶│ method Woven(...)            │──▶ dafny verify
P2 (as ghost) ──┘    alignment)           │   real P1 + ghost P2 + invs  │     (unmodified)
                                          └──────────────────────────────┘
```

* **Soundness comes from erasure.**  Dafny's ghost type system guarantees ghost statements never
  affect real state, so erasing them gives P1 back exactly (checked by a test).  P2's statements are
  woven in order, so the ghost run is a run of P2.  The one obligation is that the ghost program
  counter reaches the end at exit.  Dafny discharges it as an `assert !guard` or as termination of a
  ghost loop.
* **Alignment is placement.**  Where each ghost step sits *is* the alignment.  A guarded ghost step
  inside a real loop body is lockstep.  A ghost counter gives n:m or lagged alignment (alignment
  with memory).  A ghost condition on real state gives a data-dependent alignment.  A ghost loop is
  a run of one-sided steps.
* **Placement is found automatically.**  Nobody writes ghost code or invariants.  GhostWeave
  enumerates placements, runs each woven program on concrete inputs, and rejects placements whose
  ghost program does not finish.  It ranks the rest by how many relations between changing P1 and P2
  state hold at the loop heads, mines invariants from the traces, and prunes them with Houdini using
  Dafny as the oracle.

So yes: **this can be tested on the benchmarks.**  Ghost code does not have to be written by hand,
because the tool synthesizes it (placement, scheduling state, witnesses, invariants).  This is the
delta from WhyRel, where the user writes the alignment.

## Why weaving is sound for *any* placement: the step lemma

For a loop `W = while c { B }` of P2 and arbitrary guards `g1..gn`, which may read real state,
ghost counters or prophecy values:

```
if g1 && c {B}; ... ; if gn && c {B}; while c {B}    ≡    while c {B}
```

So a loop of P2 can be cut into guarded steps scattered anywhere in P1.  At the end, either the
remainder `while c {B}` runs as a ghost loop (exit mode `rest`; Dafny proves it terminates), or
`assert !c` is checked (exit mode `assert`).  The same argument covers an `if` of P2 whose branches
are woven under a ghost snapshot of its condition, and nested loops recursively.  The projection of
any weaving onto P2's variables is therefore P2, and **the alignment choice can never affect
soundness**.  It only affects whether the invariants are simple enough to find.  An LLM or any other
heuristic could propose placements and nothing would be at stake: Dafny rejects wrong ones.

Termination comes for free in one direction.  Dafny requires ghost code to terminate, so a proof
shows *if P1 terminates, then P2 terminates with the same result*.  That is stronger than the partial
equivalence most tools prove (see `REVE/whileif` below).

## Forall-exists, and prophecy

For ∀∃ properties (refinement, GNI), P1 is the ∀ side and its nondeterministic choices are real
havocs.  P2's choices become **ghost assignments of witness terms**.  P2's `assume`s become ghost
`assert`s, and Dafny's ghost-termination check makes the ∃ run a complete run.  Witness terms come
from a small grammar: copy the ∀ side's choice, constants, state variables, `c - v`, `l_v - r_w`.
They are filtered by running the woven program.

The grammar also contains **prophecy** witnesses: a ghost input `p` resolved at the end by
`p == l_v` for a final P1 variable.  Obligations are accumulated in a ghost flag and the method
checks `(p == l_v) ==> ok`.  This is sound because the real run never reads `p`: for each real run,
instantiate `p` with that run's final `l_v`.

`examples/prophecy/early-guess.c` shows where this is necessary.  The spec *guesses* the number of
steps of a loop over uninterpreted `f`/`p` before running it, and keeps only the run whose guess was
right.

* **With prophecy:** proved.  Lockstep weaving, `r_g := in_proph`, invariants `l_x == r_x`,
  `l_c == r_c`, resolution `in_proph == l_c`.
* **Without prophecy** (`GW_NO_PROPHECY=1`): only sequential composition is dynamically viable.  The
  witness `l_c` is available once P1 has finished, but then the ghost loop can neither be related to
  P1's loop (no closed form for f^k) nor be shown to terminate, so the proof fails.
  `early-flag.c` (eager vs lazy choice) behaves the same.

A ∀∀ product program cannot express these properties at all.  A ∀∃ alignment that picks witnesses
from the state available at the aligned point is in the same position as the no-prophecy ablation.
This is the evidence for the target theorem's second half.  A proof is not done: see "Theory" below.

## Results

See [`results/SUMMARY.md`](results/SUMMARY.md) (generated by `bench/summarize.py`) for the full
tables.  Headline numbers are filled in below from the committed result files.

<!-- RESULTS -->

## Layout

```
ghostweave/
  cfront.py         C subset -> IR (pycparser); inlining, jump elimination, doubles->reals,
                    recursion -> uninterpreted functions (mutual summaries)
  ir.py             IR; every statement carries a ghost flag
  weave.py          the weaver: plans (lockstep / lag / peel / n:m / data-dependent / nested / if)
  invariants.py     trace-based invariant mining (exact affine hull incl. bilinear terms,
                    pairwise relations, implications) + Houdini with Dafny as the oracle
  dafny.py          emission of the woven method and invocation of stock `dafny verify`
  driver.py         differential testing, plan enumeration + dynamic scoring, mutual summaries
  forall_exists.py  forall-exists mode: witness synthesis, prophecy
bench/              runners for EqBench, KestRel (forall-forall) and Elaenia (forall-exists) suites
examples/           small examples (prophecy showcase)
results/            JSONL result files (one record per benchmark, including the verified Dafny)
tests/              smoke tests (pytest)
```

## Reproducing

```bash
pip install pycparser z3-solver pytest
dotnet tool install --global dafny          # Dafny 4.11 was used
git clone https://github.com/shrBadihi/EqBench ext/EqBench
git clone https://github.com/rcdickerson/kestrel ext/kestrel
python3 bench/run_eqbench.py ext/EqBench/benchmarks results/eqbench.jsonl --jobs 4
python3 bench/run_kestrel.py ext/kestrel/benchmarks/euf results/kestrel_euf.jsonl --jobs 4
python3 bench/run_elaenia.py ext/kestrel/benchmarks/elaenia results/elaenia.jsonl --jobs 4
python3 bench/run_elaenia.py examples/prophecy results/prophecy.jsonl
python3 bench/summarize.py
```

## Semantics and limitations (read before citing numbers)

* **Idealized arithmetic.**  `int` is a mathematical integer and `double` is a real.  Math library
  functions are uninterpreted in proofs; the differential tester uses real `libm` semantics.  Proofs
  are therefore about the idealized program: a pair that differs only by floating-point
  re-association or integer overflow would count as equivalent.  C division and remainder use
  truncation semantics.  Division by zero gives an unspecified but deterministic value.
* **Partial correctness of P1.**  Real loops carry `decreases *`.  The guarantee is: if P1
  terminates then P2 terminates with an equal result.
* **Recursion.**  Recursive calls are abstracted by uninterpreted functions.  The two sides share a
  function symbol only after a mutual-summary obligation (Godlin–Strichman) is discharged
  separately.  Recursions that need induction over different unfoldings (`REVE/limit*`,
  `REVE/addhorn`, `REVE/inlining`, `REVE/triangular`) are out of reach.
* **Unsupported C:** structs, pointer arithmetic or casts (`*(long*)&x`), `goto`, `switch`
  fall-through, function pointers.
* **Invariant language:** affine equalities (including products of a loop-invariant and a
  loop-varying variable), pairwise orderings, bounds, implications guarded by loop guards or ghost
  schedule facts, sequence-length facts.  No quantified invariants, so array programs whose proof
  needs `forall i :: a[i] == b[i]` beyond whole-array equality fail.
* **Benchmarks:** the "Eq" labels of EqBench are taken as given.  A 2026 paper (Charalambous et
  al., arXiv:2607.10291) reports nine EqBench Eq pairs that are not equivalent.  Our differential
  tester also flags some (listed in the summary).

## Theory: what is and is not established

* *Every product alignment is a ghost weaving* (claimed).  The constructions that products are
  built from map directly onto weavings: sequential composition, lockstep loops with one-sided
  tails, conditional alignment, and the BiKAT/Barthe-style loop rule with left-only and right-only
  conditions.  Left-only means the ghost step is guarded off; right-only means a ghost loop inside
  the real body.  The proof is by induction on the product derivation and is written down only as
  this sketch.  The implementation covers lockstep, lag/peel, n:m, data-dependent guards, nested and
  if-structured alignments, but not ghost "run-until" loops.
* *Some weavings with prophecy have no product counterpart.*  For ∀∃ this is demonstrated by the
  examples above (an ablation, not an impossibility proof).  For ∀∀ with deterministic programs it
  is open.  Sequential composition already lets the ghost side see all of P1's past, so prophecy
  can only help when the invariant language is restricted.  That is the setting of the
  alignment-completeness results of Nagasamudram & Naumann.
