/* @ELAENIA
 * pre: forall.x_in == exists.x_in;
 * forall: impl;
 * exists: spec;
 * post: forall.x == exists.x && forall.big == exists.big;
 * especs:
 *   flip() {
 *     choiceVars: n;
 *     pre:  n == 0 || n == 1;
 *     post: ret! == n;
 *   }
 */
/* Eager vs lazy choice (Abadi & Lamport): the spec decides up front whether the result will be
   "big"; the implementation only knows after the loop. */
int f(int x);
int p(int x);
int flip();

void impl(int x_in) {
  int x = x_in;
  int big = 0;
  while (p(x) != 0) {
    x = f(x);
  }
  if (x > 100) { big = 1; }
}

void spec(int x_in) {
  int x = x_in;
  int big = flip();
  while (p(x) != 0) {
    x = f(x);
  }
  if (big == 1) { assume(x > 100); } else { assume(x <= 100); }
}
