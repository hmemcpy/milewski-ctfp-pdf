trait Monad[M[_]] {
  def flatMap[A, B](ma: M[A])(f: A => M[B]): M[B]
  def pure[A](a: A): M[A]
}