implicit def storeFunctor[S] = new Functor[Store[S, ?]] {
  def fmap[A, B](g: A => B)(fa: Store[S, A]): Store[S, B] = fa match {
    case Store(f, s) =>
      Store(g compose f, s)
  }
}