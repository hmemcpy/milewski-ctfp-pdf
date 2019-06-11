sealed trait Option[+A]
case object None extends Option[Nothing]
case class Some[A](a: A) extends Option[A]