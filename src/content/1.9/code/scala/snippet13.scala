def eval[A, B]: ((A => B), A) => B =
  (f, x) => f(x)