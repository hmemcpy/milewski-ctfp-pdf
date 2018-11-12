implicit def readerFunctor[A] = new Functor[Reader[A, ?]] {
  def fmap[X, B](f: X => B)(h: Reader[A, X]): Reader[A, B] =
    f compose h
}
