// no Rank-N types in Scala
// have to introduce a polymorphic function
trait PolyFunction1[P[_, _]] {
  def apply[A](): P[A, A]
}