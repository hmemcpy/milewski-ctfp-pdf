def prodToSum[A, B, C]: ((A, Either[B, C])) => Either[(A, B), (A, C)] = {
  case (x, e) => e match {
    case Left(y) => Left((x, y))
    case Right(z) => Right((x, z))
  }
}