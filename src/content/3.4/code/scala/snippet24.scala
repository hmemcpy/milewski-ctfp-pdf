object moreSyntax {
  // allows us to use >> as an infix operator
  implicit class MoreOps[A, B, W: Monoid](m: Writer[W, A])
      extends bindSyntax.MonadOps[A, B, W](m) {
    def >>(k: Writer[W, B]): Writer[W, B] =
      m >>= (_ => k)
  }
}