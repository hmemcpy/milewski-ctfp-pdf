def factorizer[A, B, C](p: C => A)(q: C => B): (C => (A, B)) =
  x => (p(x), q(x))