// Forall-exists (refinement): every behaviour of Impl is a behaviour of Spec.
//   Spec: x = any value in [0, 20)          Impl: x = any ODD value in [0, 20)
// Impl's choice is real (Dafny considers every possibility); Spec's choice is ghost:
// WE pick it (the "witness"), here: copy Impl's choice.
method Refinement() returns (x1: int, ghost x2: int)
  ensures x1 == x2
{
  x1 :| 0 <= x1 < 20 && x1 % 2 == 1;   // Impl: any odd number below 20 (real, nondeterministic)
  x2 := x1;                            // Spec: choose the same value (ghost witness) ...
  assert 0 <= x2 < 20;                 // ... and show it was a legal choice for Spec
}
