def factorizer[A, B, C]: (A => C) => (B => C) => Either[A, B] => C =
  i => j => {
    case Left(a) => i(a)
    case Right(b) => j(b)
  }