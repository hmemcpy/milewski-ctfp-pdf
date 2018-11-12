implicit def constFunctor[C] = new Functor[Const[C, ?]] {
  def fmap[A, B](f: A => B)(ca: Const[C, A]): Const[C, B] =
    Const(ca.v)
}