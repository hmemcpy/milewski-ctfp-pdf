trait Monad[M[_]] {
  def >=>[A, B, C](m1: A => M[B], m2: B => M[C]): A => M[C]
  def pure[A](a: A): M[A]
}