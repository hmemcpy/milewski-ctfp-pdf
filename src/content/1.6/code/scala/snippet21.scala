sealed trait Either[+A, +B]
case class Left[A](v: A) extends Either[A, Nothing]
case class Right[B](v: B) extends Either[Nothing, B]