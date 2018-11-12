implicit val optionFunctor = new Functor[Option] {
  def fmap[A, B](f: A => B)(fa: Option[A]): Option[B] = fa match {
    case None => None
    case Some(x) => Some(f(x))
  }
}