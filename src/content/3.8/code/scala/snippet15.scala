sealed trait Nat
case object Zero extends Nat
final case class Succ(n: Nat) extends Nat