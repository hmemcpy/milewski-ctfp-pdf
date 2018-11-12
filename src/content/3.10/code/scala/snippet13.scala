// Yet another type needs to be introduced.
// To read more about FunctionK (~>):
// typelevel.org/cats/datatypes/functionk.html
trait ~>[F[_], G[_]] {
  def apply[B](fa: F[B]): G[B]
}

F ~> G