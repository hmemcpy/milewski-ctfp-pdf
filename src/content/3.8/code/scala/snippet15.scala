sealed trait Nat
case object Zero extends Nat
case class Succ(n: Nat) extends Nat