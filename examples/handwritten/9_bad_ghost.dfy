// What Dafny forbids: ghost code may not influence real code.
method Bad(a: int) returns (r: int)
{
  ghost var secret := a + 1;
  r := secret;          // error: ghost value flowing into real state
}
