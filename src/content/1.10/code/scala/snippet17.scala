implicit def readerFunctor[E] = new Functor[Reader[E, ?]] {
  def fmap[A, B](f: A => B)(g: Reader[E, A]): Reader[E, B] =
    Reader(x => f(g.run(x)))
}