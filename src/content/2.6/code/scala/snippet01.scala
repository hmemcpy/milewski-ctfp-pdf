// In order to make a universal transformation,
// another type needs to be introduced.
// To read more about FunctionK (~>):
// typelevel.org/cats/datatypes/functionk.html
trait ~>[F[_], G[_]] {
  def apply[X](fa: F[X]): G[X]
}

def fromY[A, B]: (A => ?) ~> (B => ?) = new ~>[A => ?, B => ?] {
  def apply[X](f: A => X): B => X =
    b => f(btoa(b))
}