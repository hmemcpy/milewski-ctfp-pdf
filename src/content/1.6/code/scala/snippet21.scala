sealed trait Either[+A, +B]
final case class Left[A](v: A) extends Either[A, Nothing]
final case class Right[B](v: B) extends Either[Nothing, B]