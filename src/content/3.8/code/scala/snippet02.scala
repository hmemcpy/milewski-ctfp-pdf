sealed trait MonF[+A]
case object MEmpty extends MonF[Nothing]
case class MAppend[A](m: A, n: A) extends MonF[A]