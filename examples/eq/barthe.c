/* EqBench REVE/barthe: strength reduction.  P1 recomputes j each iteration, P2 increments it. */
int old_f(int n, int c) {
    int i = 0;
    int j = 0;
    int x = 0;
    while (i < n) {
        j = 5 * i + c;
        x = x + j;
        i++;
    }
    return x;
}

int new_f(int n, int c) {
    int i = 0;
    int j = c;
    int x = 0;
    while (i < n) {
        x = x + j;
        j = j + 5;
        i++;
    }
    return x;
}
