sealed trait Option[+A]
case object None extends Option[Nothing]
final case class Some[A](a: A) extends Option[A]