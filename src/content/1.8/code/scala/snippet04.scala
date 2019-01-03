implicit val eitherBifunctor = new Bifunctor[Either] {
  override def bimap[A, B, C, D](f: A => C)(g: B => D): Either[A, B] => Either[C, D] = {
    case Left(x) => Left(f(x))
    case Right(y) => Right(g(y))
  }
}