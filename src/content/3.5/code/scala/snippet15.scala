implicit def writerMonad[W: Monoid] = new Monad[Writer[W, ?]] {
  def flatMap[A, B](wa: Writer[W, A])(k: A => Writer[W, B]): Writer[W, B] =
    wa match {
      case Writer((a, w)) =>
        val ((a1, w1)) = runWriter(k(a))
        Writer((a1, Monoid[W].combine(w, w1)))
    }

  def pure[A](a: A) = Writer(a, Monoid[W].empty)
}