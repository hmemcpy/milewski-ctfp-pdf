trait FreeF[F[_], A] {
  def h[I]: I => A
  def fi[I]: F[I]
}