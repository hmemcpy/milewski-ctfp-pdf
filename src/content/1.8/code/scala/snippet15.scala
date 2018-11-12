implicit val treeFunctor = new Functor[Tree] {
  def fmap[A, B](f: A => B)(fa: Tree[A]): Tree[B] = fa match {
    case Leaf(a) => Leaf(f(a))
    case Node(t, t1) => Node(fmap(f)(t), fmap(f)(t1))
  }
}