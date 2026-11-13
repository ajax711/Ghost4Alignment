// 2:1 alignment (KestRel antonopoulos/shemer).
//   P1: y = 0; for i < 2x: y += x            P2: y = 0; for i < x: y += x;  y = 2*y
// P2 takes one step for every two steps of P1.
method TwoToOne(x: int) returns (y1: int, ghost y2: int)
  requires x >= 0
  ensures y1 == y2
{
  var i1 := 0; y1 := 0;
  ghost var i2 := 0; ghost var yy := 0;
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
}
