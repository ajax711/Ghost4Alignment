# Relational verification: where GhostWeave sits

Scope: verifying properties of two runs (of one or two programs): equivalence/regression,
k-safety (∀∀), refinement and generalized non-interference (∀∃).  arXiv full texts could not be
fetched from the build environment.  Entries marked *(abstract-level)* were checked against
abstracts and search snippets only.  Everything else comes from the papers' well-known content, or
from artifacts inspected directly (KestRel's repository, EqBench).

## 1. Reductions to unary verification

| Approach | Idea | Alignment | Notes |
|---|---|---|---|
| Self-composition (Barthe, D'Argenio, Rezk 2004; Terauchi & Aiken 2005) | run P1 then P2 | none | complete in principle, but invariants must summarize whole loops |
| Product programs (Barthe, Crespo, Kunz FM'11; Barthe et al.) | build one program interleaving both | fixed by product rules | the standard way to make invariants simple |
| Modular product programs (Eilers, Müller, Hitz, ESOP'18) | products with activation flags, in Viper | lockstep-ish | modular, handles heaps |
| Hyper Hoare Logic / Hypra (Dardinier & Müller, PLDI'24; Hypra 2024) | hyper-assertions over sets of states, encoded into Viper | none built in | covers ∀∃ and beyond |
| ∀∃ RHL into standard Hoare logic (OOPSLA'25, arXiv:2504.17444) *(abstract-level)* | an `Exec` predicate lets standard Hoare logic express ∀∃ triples | n/a | logical encoding, mechanized; not an automatic tool |
| **GhostWeave (this repo)** | P2 woven into P1 as **ghost code**; stock Dafny | **placement of ghost steps** | no product built; erasure gives soundness; prophecy is a ghost input |

How GhostWeave relates to product programs: a product is a new program whose correctness relative
to P1 and P2 must be proved once, as a meta-theorem.  A weaving *is* P1 (by erasure) plus P2 (by
the step lemma), and the unary verifier's ghost discipline checks both on every run.  Modular product
programs and Hypra also reuse a unary verifier (Viper), but they encode a product or a hyper-logic.
The closest conceptual neighbour is the prophecy/ghost machinery in Iris/ReLoC (separation logic),
which is interactive.

## 2. Alignment: who chooses it, and how

* **Manual alignment.**  WhyRel (Nagasamudram, Banerjee, Naumann; TACAS'23 prototype, STTT'25):
  the user writes a *biprogram* fixing the alignment, including alignment guards for loops.  The
  tool generates Why3 VCs.  It is the closest prior work on the "auto-active" axis.
* **Algebra of alignment.**  BiKAT (Antonopoulos, Koskinen, Le, Nagasamudram, Naumann, Ngo;
  POPL'23) gives equational laws for alignment, and "Making relational Hoare logic alignment
  complete" (Nagasamudram & Naumann, LMCS'25) shows when alignment rules are complete.  Their
  formalization also supports prophecy at intermediate points.
* **E-graphs.**  KestRel (Dickerson, Mukherjee, Delaware; OOPSLA'25, distinguished artifact) puts
  the two programs in an e-graph, saturates with BiKAT-style rewrites (loop fusion, unrolling), and
  extracts a product.  Extraction is syntactic (maximize fused loops) or semantic (simulated
  annealing with a cost from execution traces).  Invariants come from Daikon and Houdini, and the
  product goes to Dafny or SeaHorn.  *Observed in the artifact:* 31 "euf" benchmarks; 17 of the 31
  input files carry hand-written `_invariant(...)` hints.  The Elaenia extension handles ∀∃ (37
  benchmarks); the committed `results-elaenia/2025_07_07` logs show 19/37 verified in their
  "noalign" configuration.
* **Data-driven alignment.**  Churchill, Padon, Sharma, Aiken (PLDI'19) align concrete traces to
  build a product for equivalence checking of x86 code.  Property-directed self-composition
  (Shemer, Gurfinkel, Shoham, Vizel; CAV'19) searches compositions together with invariants.
* **Reinforcement learning.**  Chen, Wei, Feng, Bastani, Dillig (OOPSLA'19) cast the choice of
  product-construction rules as an MDP and learn a policy for it.
* **Constraint solving.**  PCSat / pfwCSP (Unno, Terauchi, Koskinen; CAV'21) adds well-founded and
  functional predicate variables to CHCs.  Functional predicates are Skolem functions for ∃
  choices, so alignment and witnesses are synthesized as part of constraint solving.  Reported: 20
  problems, 15 solved automatically and 5 semi-automatically *(abstract-level)*.
* **Regression verification and mutual summaries.**  Godlin & Strichman; SymDiff (Lahiri et al.);
  mutual summaries (Hawblitzel et al., CADE'13); REVE (Felsing et al., ASE'14), which is the source
  of EqBench's REVE pairs.  Recursive calls are related through uninterpreted functions.
  GhostWeave reuses the Godlin–Strichman rule for recursion.

## 3. ∀∃ and prophecy

* RHLE (Dickerson, Ye, Delaware; ESOP'22): ∀∃ Hoare logic, with the ∃ side's choices given by
  specifications (the `especs` of the Elaenia suite).
* ForEx and "∀∃ by filtering to ∀∀" (arXiv:2509.04777, 2025) *(abstract-level)*: reduce ∀∃ to ∀∀
  by restricting the ∃ side.
* Prophecy variables for hyperproperties (Beutner & Finkbeiner, arXiv:2206.01797): strategy-based
  verification of ∀*∃* is incomplete, and adding prophecies makes it complete.  This is the
  theoretical reason the prophecy witness in GhostWeave matters.  Our `early-guess.c` is a minimal
  program-level instance.

## 4. Benchmarks

* **EqBench** (Badihi, Li, Rubin; MSR'21): 272 pairs in C and Java.  248 pairs (135 Eq, 113 Neq)
  have per-pair metadata; the remaining 24 are whole-program aggregates.  The pairs come from
  REVE, CLEVER (client-specific: equivalence holds only for the client `main`), Numerical Recipes
  style numeric code (airy, bess, gam, ell, ...), tcas, tsafe, etc.
* **EquiBench** (Wei et al., EMNLP'25): 2400 pairs in four languages and six categories, built to
  test LLM reasoning.  Only the categories with small, verifier-friendly programs suit a deductive
  tool.  Not run here.
* **KestRel suites**: `euf` (31; Barthe, Antonopoulos, Sousa & Dillig's comparator antisymmetry,
  Unno, Churchill, ADT examples) and `elaenia` (37 ∀∃).
* PCSat's 20 problems overlap with the Unno-derived KestRel/Elaenia benchmarks.

## 5. LLMs and equivalence (2025–2026)

* *Partial Contracts Suffice: Sound, LLM-Inferred Regression Verification* (Charalambous, Menezes,
  Sun, Cordeiro; arXiv:2607.10291, July 2026) *(abstract-level)*: contract-based regression
  verification with LLM-inferred partial contracts.  On EqBench-C it reports no false proofs and
  nine pairs labeled Eq that are not equivalent.
* VeriEquivBench (ICLR'26) *(abstract-level)*: equivalence of LLM-generated Dafny code and specs.
* The pattern matches GhostWeave's search argument: an untrusted proposer (LLM, heuristic, e-graph
  extraction) plus a sound checker.  In GhostWeave the proposer's output is a *placement plan* and
  witness terms, and soundness never depends on it.
