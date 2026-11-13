// Equivalence of two loop-free programs (EqBench airy/Sign).
// P1 is real code, P2 is ghost code. Both read the same input (a, b).
method Sign(a: real, b: real) returns (r1: real, ghost r2: real)
  ensures r1 == r2
{
  // P1 (real)
  if b >= 0.0 {
    if a >= 0.0 { r1 := a; } else { r1 := -a; }
  } else {
    if a >= 0.0 { r1 := -a; } else { r1 := a; }
  }
  // P2 (ghost)
  if (a >= 0.0 && b >= 0.0) || (a < 0.0 && b < 0.0) { r2 := a; } else { r2 := -a; }
}
