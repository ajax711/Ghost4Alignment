// Non-interference: the public output must not depend on the secret input.
// Two runs of the SAME program, same `low`, arbitrary different secrets h1, h2.
//   int f(int low, int high) {
//     int r = 0, i = 0;
//     while (i < low) { if (high > 0) r = r + 2; else r = r + 1 + 1; i++; }
//     return r;
//   }
method NonInterference(low: int, h1: int, ghost h2: int) returns (r1: int, ghost r2: int)
  ensures r1 == r2                  // no secret flows to the output
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
