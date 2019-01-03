// with the Kind Projector plugin:
implicit def function1Functor[R] = new Functor[R => ?] {
  def fmap[A, B](f: A => B)(g: R => A): (R => B) =
    f compose g
}