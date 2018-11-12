def factorizer[A, B, C](g: (A, B) => C): A => (B => C) =
  a => (b => g(a, b))