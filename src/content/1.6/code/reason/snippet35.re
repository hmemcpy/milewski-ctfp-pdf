let sum_to_prod =
  fun
  | Left(x, y) => (x, Left(y))
  | Right(x, z) => (x, Right(z));
