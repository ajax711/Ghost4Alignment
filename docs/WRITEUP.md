# Relational verification with ghost code: a short introduction

This note assumes no background in programming languages or deductive verification beyond
Ulbrich's survey.  Every example below is a real Dafny file in
[`examples/handwritten/`](../examples/handwritten), and all of them are checked by the unmodified
Dafny verifier (`dafny verify <file>`).

---

## 1. Deductive verification in five minutes

A *deductive verifier* (Dafny, Why3, Frama-C, KeY, Viper) checks a program against a
specification and either proves it for **all** inputs or reports what it could not prove.  A
specification has two parts:

* `requires P`, the **precondition**: what we may assume about the inputs.
* `ensures Q`, the **postcondition**: what must hold when the method returns.

Straight-line code and `if` statements are handled automatically.  The verifier turns the program
into a logical formula and asks an SMT solver (Z3) whether it is valid.

**Loops are the hard part.**  The verifier cannot unroll a loop an unknown number of times, so you
give it a **loop invariant**: a fact that holds every time the loop condition is checked.  Dafny
checks two things:

1. the invariant holds when the loop is first reached, and
2. if it holds at the start of an iteration, it still holds at the end of that iteration.

After the loop, the verifier knows only "the invariant holds and the loop condition is false".
Everything it knows about the loop must be in the invariant.

```dafny
// sum of 0..n-1
var i := 0; var s := 0;
while i < n
  invariant 0 <= i <= n          (when n >= 0)
  invariant s == i * (i - 1) / 2 // a "functional" invariant: the whole meaning of the loop so far
{ s := s + i; i := i + 1; }
```

Finding invariants is the main cost of deductive verification.  Keep this in mind for the next
section.

---

## 2. Relational properties, and why we need alignment

Most specifications talk about **one run** of a program, for example "the result is sorted".
*Relational* properties talk about **two runs**, of the same program or of two different
programs:

| Property | The two runs | Postcondition relates them by |
|---|---|---|
| **Equivalence / regression** (did my refactoring change behaviour?) | old program, new program, same input | equal outputs |
| **Non-interference** (does the secret leak?) | same program, same public input, *different* secrets | equal public outputs |
| **Monotonicity** | same program, inputs `n1 <= n2` | `out1 <= out2` |
| **Refinement** (implementation vs nondeterministic spec) | every implementation run has *some* matching spec run | equal outputs |

The first three are **∀∀** ("for all pairs of runs") properties.  Refinement is **∀∃** ("for every
run of A there exists a run of B").

### The naive approach: self-composition

The oldest trick is to rename the variables of the second run and **run the two programs one
after the other**, then check the relation at the end.  This is called *self-composition*.  It is
correct, but it makes the invariants hard.

Take the two programs from EqBench `REVE/barthe`:

```c
// P1                                   // P2
int i = 0, j = 0, x = 0;                int i = 0, j = c, x = 0;
while (i < n) {                         while (i < n) {
  j = 5*i + c;                            x = x + j;
  x = x + j;                              j = j + 5;
  i++;                                    i++;
}                                       }
return x;                               return x;
```

With self-composition (P1's loop, then P2's loop), P1's loop invariant has to say *what x is*:
`x1 == 5*i1*(i1-1)/2 + c*i1`.  P2's loop needs the same closed form, and then the solver must prove
the two formulas equal.  That works here, but it is nonlinear arithmetic.  For realistic code
(arrays, floating point, unknown library functions) there often *is no* closed form.

### The better approach: run the loops side by side

Execute **one iteration of P1, then one iteration of P2**, in the same loop.  The invariant only
has to say that *the two runs agree so far*:

```
i1 == i2   &&   x1 == x2   &&   j2 == 5*i1 + c
```

Nothing here describes what the loop computes.  It only relates the two runs, which is much
easier, both for a human and for an automatic invariant finder.

**Alignment** is the decision of *which steps of run 1 are executed together with which steps of
run 2*.  A good alignment keeps the two runs "close", so the relational invariant stays simple.
The alignment is not always "one step each" (lockstep):

* P1 does one extra useless iteration at the start → P2 must **skip** P1's first iteration (§5.3).
* P1 loops `2x` times while P2 loops `x` times → P2 takes **one step every two** steps of P1 (§5.4).
* P2's extra iterations happen only at the end → finish P2 **alone** after P1 is done (§5.6).
* Sometimes the choice depends on the data ("step P2 only when P1's branch was taken").

Classic tools *build a third program*, the **product program**, that interleaves P1 and P2
according to an alignment, and then verify that.  KestRel (OOPSLA'25) searches the space of
products with e-graphs, and WhyRel asks the user to write the alignment by hand.  Building the
product is the delicate part: you must prove, once and for all, that the product behaves like P1
and P2 together.

---

## 3. What is ghost code?

**Ghost code** is code that exists only for the proof.  It is ordinary statements and variables,
marked `ghost`.  The verifier enforces one rule:

> **Ghost code may read real variables, but it can never influence them.**  No assignment from a
> ghost variable into a real one, no ghost condition deciding a real branch, no ghost loop that
> might not terminate.

Because of this rule, deleting all ghost code (*erasure*) leaves the original program exactly
as it was, behaving exactly the same.  Ghost code is like a notebook the proof keeps next to the
running program.  It can record and compute anything, but it cannot reach in and change things.

Dafny rejects a violation ([`9_bad_ghost.dfy`](../examples/handwritten/9_bad_ghost.dfy)):

```dafny
method Bad(a: int) returns (r: int) {
  ghost var secret := a + 1;
  r := secret;   // Error: ghost variables are allowed only in specification contexts
}
```

Ghost code is normally used for small things, such as a counter, a copy of an old value, or an
abstract model of a data structure.  Our idea uses it for something bigger.

---

## 4. The idea: write P2 *inside* P1 as ghost code

> Take P1 as it is (real code).  Insert P2's statements, in their original order, as **ghost**
> code at chosen places inside P1.  Then hand this single program to a normal verifier, with
> the relational property as its postcondition.

No product program is built and no special relational verifier is needed: Dafny, Frama-C, KeY or
Viper can check it as it is.

**Why is this sound?**

1. **The real run is exactly P1.**  Erase the ghost code and you get P1 back.  The verifier's
   ghost rule guarantees the ghost part never changed anything real.
2. **The ghost run is exactly P2.**  P2's statements appear in order.  A loop of P2 is cut into
   *guarded steps* (`if guard { body }`) placed inside P1's loop.  Executing some guarded steps
   and then the rest of the loop is the same as executing the loop:

   ```
   if c {B};  if c {B};  ...;  while c {B}    ≡    while c {B}
   ```

   The one obligation is that **the ghost run has finished when the method exits**: either
   `assert !c` ("P2's loop is done"), or the remaining loop runs as a ghost loop.  Dafny then
   requires that ghost loop to terminate.
3. So the verified postcondition relates a real run of P1 to a real run of P2.

**The placement *is* the alignment.**  Where you put P2's steps decides which steps run together.
Placement can never make the proof *wrong*: any placement gives a correct encoding.  A bad
placement only makes the invariants harder or impossible to find, in which case the verifier says
"cannot prove".  This is why the search for a placement can be done by a heuristic, a random
search or an LLM: wrong guesses are rejected by the verifier and never accepted.

Two things ghost code gives you that a product program does not have directly:

* **Memory.**  Ghost variables can record anything about the past (a counter, a flag "first
  iteration done").  Such scheduling decisions are just more ghost code.
* **Prophecy.**  A ghost variable can stand for a value from the *future* (§5.8).

---

## 5. Worked examples (all verified by Dafny)

Naming convention: `x1` is P1's variable (real), `x2` is P2's copy (ghost).  Both runs get the same
inputs unless stated otherwise.

### 5.1 Equivalence without loops: [`1_sign.dfy`](../examples/handwritten/1_sign.dfy)

Two versions of a sign-flipping function (EqBench `airy/Sign`).  With no loops, the placement
does not matter: put P2 after P1.

```dafny
method Sign(a: real, b: real) returns (r1: real, ghost r2: real)
  ensures r1 == r2
{
  // P1 (real)
  if b >= 0.0 { if a >= 0.0 { r1 := a; } else { r1 := -a; } }
  else        { if a >= 0.0 { r1 := -a; } else { r1 := a; } }
  // P2 (ghost)
  if (a >= 0.0 && b >= 0.0) || (a < 0.0 && b < 0.0) { r2 := a; } else { r2 := -a; }
}
```

Dafny checks all four sign combinations symbolically.  No invariant is needed.

### 5.2 Equivalence with loops, lockstep: [`2_lockstep.dfy`](../examples/handwritten/2_lockstep.dfy)

The `barthe` pair from §2.  One P2 step is placed at the end of every P1 iteration:

```dafny
method StrengthReduction(n: int, c: int) returns (x1: int, ghost x2: int)
  ensures x1 == x2
{
  var i1 := 0; var j1 := 0; x1 := 0;              // P1 state (real)
  ghost var i2 := 0; ghost var j2 := c; x2 := 0;  // P2 state (ghost)
  while i1 < n
    invariant i1 == i2 && x1 == x2      // the two runs agree ...
    invariant j2 == 5 * i1 + c          // ... and P2's j is the j P1 will compute next
  {
    j1 := 5 * i1 + c; x1 := x1 + j1; i1 := i1 + 1;              // one iteration of P1
    if i2 < n { x2 := x2 + j2; j2 := j2 + 5; i2 := i2 + 1; }    // one iteration of P2 (ghost)
  }
  assert !(i2 < n);   // exit obligation: P2's loop has finished too
}
```

Compare with self-composition: no closed-form sum appears anywhere.

### 5.3 Off-by-one: P2 skips P1's first iteration: [`3_lag.dfy`](../examples/handwritten/3_lag.dfy)

```c
// P1: for (i = 0; i <= n; i++) x += i;      // first iteration adds 0
// P2: for (j = 1; j <= n; j++) x += j;
```

Lockstep fails: after one step P1 has added 0 and P2 has added 1.  A **ghost flag** remembers
whether this is the first iteration, and P2 sits it out:

```dafny
  ghost var first := true;            // ghost scheduling state ("alignment memory")
  while i <= n
    invariant x1 == x2
    invariant first ==> i == 0 && j == 1
    invariant !first ==> j == i
  {
    x1 := x1 + i; i := i + 1;                              // P1 step
    if !first && j <= n { x2 := x2 + j; j := j + 1; }      // P2 step, skipped the first time
    first := false;
  }
  assert !(j <= n);
```

The invariant has two cases ("before the first step" and "after it").  Our tool generates this
kind of invariant automatically from the ghost schedule.

### 5.4 2:1 alignment: [`4_two_to_one.dfy`](../examples/handwritten/4_two_to_one.dfy)

```c
// P1: y = 0; for (i = 0; i < 2*x; i++) y += x;
// P2: y = 0; for (i = 0; i < x;   i++) y += x;   y = 2*y;
```

P2 takes a step only on every second iteration of P1.  The guard reads the real counter, which is
allowed because ghost code may read real variables:

```dafny
  while i1 < 2 * x
    invariant 0 <= i1 <= 2 * x
    invariant i1 % 2 == 0 ==> i1 == 2 * i2 && y1 == 2 * yy
    invariant i1 % 2 == 1 ==> i1 == 2 * i2 + 1 && y1 == 2 * yy + x
  {
    y1 := y1 + x; i1 := i1 + 1;
    if i1 % 2 == 0 && i2 < x { yy := yy + x; i2 := i2 + 1; }   // P2 steps every other time
  }
  assert !(i2 < x);
  y2 := 2 * yy;
```

A product-program tool would instead *unroll* P1's loop twice.  With ghost code, P1 stays
untouched and the schedule lives in the guard.

### 5.5 Non-interference: [`5_noninterference.dfy`](../examples/handwritten/5_noninterference.dfy)

Same program twice, same public input `low`, **different** secrets `h1` and `h2`.  The secret
affects which branch runs but not the result:

```c
int f(int low, int high) {
  int r = 0, i = 0;
  while (i < low) { if (high > 0) r = r + 2; else r = r + 1 + 1; i++; }
  return r;
}
```

```dafny
method NonInterference(low: int, h1: int, ghost h2: int) returns (r1: int, ghost r2: int)
  ensures r1 == r2                  // the output does not depend on the secret
{
  var i1 := 0; r1 := 0;
  ghost var i2 := 0; r2 := 0;
  while i1 < low
    invariant i1 == i2 && r1 == r2
  {
    if h1 > 0 { r1 := r1 + 2; } else { r1 := r1 + 1 + 1; } i1 := i1 + 1;   // run 1 (real)
    if i2 < low {                                                         // run 2 (ghost)
      if h2 > 0 { r2 := r2 + 2; } else { r2 := r2 + 1 + 1; } i2 := i2 + 1;
    }
  }
  assert !(i2 < low);
}
```

Because `h1` and `h2` are independent, Dafny considers every combination of secrets.

### 5.6 Monotonicity, and a ghost loop on its own: [`6_monotone.dfy`](../examples/handwritten/6_monotone.dfy)

`f(n) = 3 + 3 + ... (n times)`.  We prove that `n1 <= n2` implies `f(n1) <= f(n2)`.  The runs move
in lockstep while both are running.  Then run 2's extra iterations execute as a separate **ghost
loop**, the "one-sided steps":

```dafny
method Monotone(n1: int, ghost n2: int) returns (s1: int, ghost s2: int)
  requires n1 <= n2
  ensures s1 <= s2
{
  var i1 := 0; s1 := 0;
  ghost var i2 := 0; s2 := 0;
  while i1 < n1
    invariant i1 == i2 && s1 == s2
  { s1 := s1 + 3; i1 := i1 + 1;
    if i2 < n2 { s2 := s2 + 3; i2 := i2 + 1; } }
  while i2 < n2            // ghost loop: the rest of run 2 (Dafny proves it terminates)
    invariant s1 <= s2
  { s2 := s2 + 3; i2 := i2 + 1; }
}
```

### 5.7 Refinement (∀∃): [`7_refinement.dfy`](../examples/handwritten/7_refinement.dfy)

A *specification* may be nondeterministic ("return any number below 20").  An implementation
refines it if **every** implementation behaviour is **some** spec behaviour.  This is ∀∃: for
each run of Impl we must *exhibit* a matching run of Spec.

In ghost code this is natural:

* the implementation's nondeterministic choice is **real**, so Dafny considers every possibility;
* the spec's choice is **ghost**, so *we* pick it (the *witness*), and we must show the pick was
  legal for the spec.

```dafny
//   Spec: x = any value in [0, 20)          Impl: x = any ODD value in [0, 20)
method Refinement() returns (x1: int, ghost x2: int)
  ensures x1 == x2
{
  x1 :| 0 <= x1 < 20 && x1 % 2 == 1;   // Impl's choice: any odd number below 20 (real)
  x2 := x1;                            // Spec's choice: we pick the same value (ghost witness) ...
  assert 0 <= x2 < 20;                 // ... and show it was a legal choice for Spec
}
```

### 5.8 Prophecy: choosing a witness from the future: [`8_prophecy.dfy`](../examples/handwritten/8_prophecy.dfy)

Now the spec has to make its choice *early*, before a loop, while the implementation only learns
the right value *after* the loop:

```c
// Impl: x = x0; c = 0; while (p(x)) { x = f(x); c++; }
// Spec: g = guess(); x = x0; c = 0; while (p(x)) { x = f(x); c++; }  assume(c == g);
```

`f` and `p` are unknown functions, so there is no formula for the number of steps.  We want the
loops in lockstep (the only way to relate `x1` and `x2` is `x1 == x2` step by step).  But at the
point where Spec guesses, Impl has not run its loop yet.

A **prophecy variable** solves this.  It is a ghost input `N` that stands for "the value Impl's
counter *will* have at the end".  We use it early and *resolve* it at the end: the postcondition
only has to hold for the `N` that turns out to be right.

```dafny
method EarlyGuess(x0: int, ghost N: int)
    returns (x1: int, c1: int, ghost x2: int, ghost g: int, ghost ok: bool)
  ensures N == c1 ==> (ok && x1 == x2 && c1 == g)    // for the right N, Spec's run matches
  decreases *
{
  x1 := x0; c1 := 0;
  x2 := x0; g := N;               // Spec's early guess := the prophecy
  ghost var c2 := 0;
  while p(x1)
    invariant x1 == x2 && c1 == c2
    decreases *
  { x1 := f(x1); c1 := c1 + 1;                       // Impl step
    if p(x2) { x2 := f(x2); c2 := c2 + 1; } }        // Spec step (ghost)
  assert !p(x2);
  ok := (c2 == g);                // Spec's assume(c == g) holds
}
```

Why this is sound: the real code never reads `N`, so the implementation's run is the same for every
`N`.  Take any implementation run and set `N` to its final counter.  The postcondition then says
the ghost run (a legal Spec run, guess included) matches.

Without prophecy, the only way to know the right guess is to run Impl completely *first*.  But
then the loops cannot be related step by step, and the proof fails.  Our tool shows exactly that
(§6).  This is the sense in which ghost weaving can do more than product programs.

---

## 6. What the tool (GhostWeave) automates

Writing §5 by hand means choosing the placement, the schedule (flags, counters, guards), the
witnesses and the invariants.  GhostWeave does all of these automatically for C programs:

1. **Translate** both C programs to a small internal language.
2. **Enumerate placements**: lockstep, skip-first, lead-by-one, k:1 and 1:k, nested loops,
   branch-by-branch, run P2 afterwards, data-dependent guards.
3. **Run** each woven program on random inputs.  Throw away placements where the ghost run does
   not finish ("counterexample-guided": a failing run tells you the placement is wrong).  Rank the
   rest by how many simple relations between run 1 and run 2 hold at the loop heads.
4. **Guess invariants** from the recorded states (equalities, linear relations, case splits like
   in §5.3/§5.4).  Keep only those Dafny can prove (the Houdini algorithm).
5. **Check** the woven program with stock Dafny.  For ∀∃ properties, also search witnesses: copy
   the implementation's choice, constants, simple expressions, or a prophecy.

**Current status, stated honestly:**

* No non-equivalent pair has ever been "proved".
* It found the alignments of §5.2–5.4 on real benchmark pairs by itself, and proved both prophecy
  examples, which fail with prophecy disabled.
* On EqBench only a partial run exists: 12/18 equivalent pairs proved, and all 14 non-equivalent
  pairs refuted with concrete counterexamples.  On the ∀∃ suite: 11/29 so far.
* It is slow when it fails, because it restarts Dafny on every invariant-pruning round.
* It has no invariants with quantifiers or division, and no structs.

Details are in the [README](../README.md); the literature map is in
[LITERATURE.md](LITERATURE.md).

---

## Glossary

* **Invariant**: a fact true every time a loop condition is checked; how a verifier reasons about
  loops.
* **Relational property**: a property relating two runs (equivalence, non-interference,
  monotonicity, refinement).
* **∀∀ / ∀∃**: "for all pairs of runs" versus "for every run of A there is a run of B".
* **Self-composition**: run one copy after the other.  Correct, but needs hard invariants.
* **Product program**: a third program interleaving both, according to an alignment.
* **Alignment**: which steps of run 1 execute together with which steps of run 2.
* **Ghost code**: proof-only code that may read but never change real state; erasing it gives
  back the original program.
* **Weaving**: placing P2's statements into P1 as ghost code.  Here, placement = alignment.
* **Witness**: the value we pick for the "exists" side's nondeterministic choice.
* **Prophecy variable**: a ghost value standing for something that is only known later; it is
  used early and pinned down ("resolved") at the end.
* **Houdini**: start with many candidate invariants and repeatedly drop the ones the verifier
  rejects, until the rest are all provable.
