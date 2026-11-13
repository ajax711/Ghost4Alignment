// Equivalence with loops, lockstep alignment (EqBench REVE/barthe, "strength reduction").
//   P1: j = 5*i + c recomputed every iteration      P2: j starts at c, j = j + 5
method StrengthReduction(n: int, c: int) returns (x1: int, ghost x2: int)
  ensures x1 == x2
{
  var i1 := 0; var j1 := 0; x1 := 0;           // P1 state (real)
  ghost var i2 := 0; ghost var j2 := c; x2 := 0;  // P2 state (ghost)
  while i1 < n
    invariant i1 == i2 && x1 == x2      // the two runs agree ...
    invariant j2 == 5 * i1 + c          // ... and P2's j is the j P1 will compute next
  {
    j1 := 5 * i1 + c; x1 := x1 + j1; i1 := i1 + 1;              // one iteration of P1
    if i2 < n { x2 := x2 + j2; j2 := j2 + 5; i2 := i2 + 1; }    // one iteration of P2 (ghost)
  }
  assert !(i2 < n);   // exit obligation: P2's loop is finished too
}
