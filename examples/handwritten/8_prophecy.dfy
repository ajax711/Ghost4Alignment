// Prophecy: the Spec must guess, BEFORE its loop, how many steps the loop will take.
//   Impl: x = x0; c = 0; while (p(x)) { x = f(x); c++; }
//   Spec: g = guess(); x = x0; c = 0; while (p(x)) { x = f(x); c++; }  assume(c == g);
// f and p are unknown functions, so the step count has no formula. The witness for the guess
// is a prophecy N: a ghost input that we only *resolve* at the end (N == Impl's final c).
function f(x: int): int
function p(x: int): bool

method EarlyGuess(x0: int, ghost N: int) returns (x1: int, c1: int, ghost x2: int, ghost g: int, ghost ok: bool)
  ensures N == c1 ==> (ok && x1 == x2 && c1 == g)    // for the right N, Spec's run matches
  decreases *
{
  x1 := x0; c1 := 0;
  x2 := x0; g := N;               // Spec's early guess := the prophecy
  ghost var c2 := 0;
  while p(x1)
    invariant x1 == x2 && c1 == c2
    decreases *
  {
    x1 := f(x1); c1 := c1 + 1;                       // Impl step
    if p(x2) { x2 := f(x2); c2 := c2 + 1; }          // Spec step (ghost)
  }
  assert !p(x2);
  ok := (c2 == g);                // Spec's assume(c == g) holds
}
