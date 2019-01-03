// Another type needs to be introduced.
// To read more about FunctionK (~>):
// typelevel.org/cats/datatypes/functionk.html
trait ~>[F[_], G[_]] {
  def apply[C](fa: F[C]): G[C]
}

trait Ran[K[_], D[_], A] {
  // partially-applied type
  type AtoK[I] = A => K[I]

  def apply: AtoK ~> D
}