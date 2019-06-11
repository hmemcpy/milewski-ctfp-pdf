def fmap[A, B](f: A => B)(fa: List[A]): List[B] = fa match {
  case Cons(x, t) => Cons(f(x), fmap(f)(t))
}