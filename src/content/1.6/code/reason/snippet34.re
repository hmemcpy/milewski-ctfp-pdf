let prod_to_sum = ((x, e)) =>
  switch (e) {
  | Left(y) => Left(x, y)
  | Right(z) => Right(x, z)
  };
