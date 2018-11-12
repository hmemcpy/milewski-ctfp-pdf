def sumToProd[A, B, C]: Either[(A, B), (A, C)] => (A, Either[B, C]) = {
  case Left((x, y)) => (x, Left(y))
  case Right((x, z)) => (x, Right(z))
}