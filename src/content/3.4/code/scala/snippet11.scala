object bindSyntax {
  //allows us to use flatMap as an infix operator
  implicit class MonadOps[A, B, W: Monoid](wa: Writer[W, A]) {
    def flatMap(f: A => Writer[W, B]): Writer[W, B] = wa match {
      case Writer((a, w1)) =>
        val Writer((b, w2)) = f(a)
        Writer(b, Monoid[W].combine(w1, w2))
    }
  }
}