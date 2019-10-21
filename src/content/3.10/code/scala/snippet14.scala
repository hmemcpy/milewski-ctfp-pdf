sealed trait Coend[P[_, _]]
final case class DiagP[A](p: P[A, A]) extends Coend[P]
