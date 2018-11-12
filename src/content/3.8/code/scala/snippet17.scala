sealed trait NatF[+A]
case object ZeroF extends NatF[Nothing]
final case class SuccF[A](a: A) extends NatF[A]