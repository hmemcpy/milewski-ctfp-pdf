trait `PolyFunctionM`[F[_], G[_]] {
  def apply[I: Monoid](fa: F[I]): G[I]
}

trait Lst[A] {
  type aTo[X] = A => X

  def apply(): aTo `PolyFunctionM` Id
}