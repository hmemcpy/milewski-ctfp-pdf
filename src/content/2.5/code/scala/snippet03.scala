// In order to make a universal transformation,
// another type needs to be introduced.
// To read more about FunctionK (~>):
// typelevel.org/cats/datatypes/functionk.html
trait ~>[F[_], G[_]] {
  def apply[B](fa: F[B]): G[B]
}

// Kind Projector plugin provides
// a more concise syntax for type lambdas:
def alpha[A]: (A => ?) ~> F