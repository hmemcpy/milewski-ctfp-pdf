implicit def readerFunctor[R] = new Functor[Reader[R, ?]] {
  def fmap[A, B](f: A => B)(g: Reader[R, A]): Reader[R, B] =
    f compose g
}