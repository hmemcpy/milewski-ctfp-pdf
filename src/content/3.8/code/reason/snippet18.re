let rec fib =
  fun
  | ZeroF => (1, 1)
  | SuccF(m, n) => (n, m + n);
