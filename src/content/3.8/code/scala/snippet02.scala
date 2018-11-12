sealed trait MonF[+A]
case object MEmpty extends MonF[Nothing]
final case class MAppend[A](m: A, n: A) extends MonF[A]