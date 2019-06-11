trait Comonad[W[_]] extends Functor[W] {
  def =>=[A, B, C](w1: W[A] => B)(w2: W[B] => C): W[A] => C
  def extract[A](wa: W[A]): A
}