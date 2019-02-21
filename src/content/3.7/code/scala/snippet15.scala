trait Comonad[W[_]] extends Functor[W] {
  def extract[A](wa: W[A]): A

  def duplicate[A](wa: W[A]): W[W[A]] =
    extend(identity[W[A]])(wa)

  def extend[A, B](f: W[A] => B)(wa: W[A]): W[B] =
    (fmap(f) _ compose duplicate)(wa)
}