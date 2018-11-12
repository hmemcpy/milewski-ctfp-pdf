implicit def readerMonad[E] = new Monad[Reader[E, ?]] {
  def pure[A](x: A): Reader[E, A] =
    Reader(e => x)
  
  def flatMap[A, B](ra: Reader[E, A])(k: A => Reader[E, B]): Reader[E, B] =
    Reader(e =>
      runReader(k(runReader(ra)(e)))(e))
}