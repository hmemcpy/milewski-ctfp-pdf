implicit val listFunctor = new Functor[List] {
  def fmap[A, B](f: A => B)(fa: List[A]): List[B] = fa match {
    case Nil => Nil
    case Cons(x, t) => Cons(f(x), fmap(f)(t))
  }
}