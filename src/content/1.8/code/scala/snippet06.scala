implicit val identityFunctor = new Functor[Id] {
  def fmap[A, B](f: A => B)(x: Id[A]): Id[B] =
    f(x)
}