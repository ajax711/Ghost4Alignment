// Monotonicity:  n1 <= n2  ==>  f(n1) <= f(n2),   f(n) = 3 + 3 + ... (n times)
// Lockstep while both run, then the rest of run 2 as a ghost loop on its own.
method Monotone(n1: int, ghost n2: int) returns (s1: int, ghost s2: int)
  requires n1 <= n2
  ensures s1 <= s2
{
  var i1 := 0; s1 := 0;
  ghost var i2 := 0; s2 := 0;
  while i1 < n1
    invariant i1 == i2 && s1 == s2
  {
    s1 := s1 + 3; i1 := i1 + 1;
    if i2 < n2 { s2 := s2 + 3; i2 := i2 + 1; }
  }
  while i2 < n2            // ghost loop: run 2's remaining iterations (Dafny proves it terminates)
    invariant s1 <= s2
  {
    s2 := s2 + 3; i2 := i2 + 1;
  }
}
