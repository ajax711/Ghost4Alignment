/* @ELAENIA
 * pre: forall.x_in == exists.x_in;
 * forall: impl;
 * exists: spec;
 * post: forall.x == exists.x && forall.c == exists.g;
 * especs:
 *   guess() {
 *     choiceVars: n;
 *     pre:  true;
 *     post: ret! == n;
 *   }
 */
/* The spec guesses the number of steps *before* running the loop and keeps only the run whose
   guess was right.  f and p are uninterpreted, so the step count has no closed form: the witness
   for the guess is a prophecy of the implementation's final counter. */
int f(int x);
int p(int x);
int guess();

void impl(int x_in) {
  int x = x_in;
  int c = 0;
  while (p(x) != 0) {
    x = f(x);
    c = c + 1;
  }
}

void spec(int x_in) {
  int x = x_in;
  int g = guess();
  int c = 0;
  while (p(x) != 0) {
    x = f(x);
    c = c + 1;
  }
  assume(c == g);
}
