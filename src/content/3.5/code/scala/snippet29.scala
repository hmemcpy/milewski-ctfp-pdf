implicit def contMonad[R] = new Monad[Cont[R, ?]] {
  def flatMap[A, B](ka: Cont[R, A])(kab: A => Cont[R, B]): Cont[R, B] =
    Cont { hb =>
      runCont(ka)(a => runCont(kab(a))(hb))
    }

  def pure[A](a: A): Cont[R, A] =
    Cont(ha => ha(a))
}