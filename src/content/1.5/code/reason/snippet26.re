let factorizer = (i, j) =>
  fun
  | Left(a) => i(a)
  | Right(b) => j(b);
