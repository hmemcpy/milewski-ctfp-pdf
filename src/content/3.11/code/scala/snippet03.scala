type Id[I] = I

trait PolyFunc[A, K[_]] {
  type AtoK[I] = A => K[I]

  def apply(): AtoK ~> Id
}