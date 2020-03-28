let rec sum_s = (n, Cons(x, xs)) =>
  n <= 0 ? 0 : x + sum_s(n - 1, Lazy.force(xs))
