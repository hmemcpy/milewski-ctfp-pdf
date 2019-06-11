case class Writer[W, A](run: (A, W))

implicit def writerFunctor[W] = new Functor[Writer[W, ?]] {
  def fmap[A, B](f: A => B)(fa: Writer[W, A]): Writer[W, B] =
    fa match {
      case Writer((a, w)) => Writer(f(a), w)
  }
}