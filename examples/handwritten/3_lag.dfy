// Off-by-one alignment (EqBench REVE/barthe2).
//   P1: for i = 0..n: x += i            P2: for j = 1..n: x += j
// P1 does one extra (useless) iteration first, so P2 must skip P1's first iteration.
method Lag(n: int) returns (x1: int, ghost x2: int)
  ensures x1 == x2
{
  var i := 0; x1 := 0;
  ghost var j := 1; x2 := 0;
  ghost var first := true;            // ghost scheduling state: "alignment memory"
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
}
