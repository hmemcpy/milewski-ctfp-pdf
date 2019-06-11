implicit val streamFunctor = new Functor[Stream] {
  def fmap[A, B](f: A => B)(fa: Stream[A]): Stream[B] = fa match {
    case Stream(a, as) =>
      Stream(() => f(a()), () => fmap(f)(as()))
  }
}