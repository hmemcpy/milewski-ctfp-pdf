implicit def freeFunctor[F[_]] = new Functor[FreeF[F, ?]] {
  def fmap[A, B](g: A => B)(fa: FreeF[F, A]): FreeF[F, B] = fa match {
    case FreeF(r) => FreeF {
      new ~>[B => ?, F] {
        def apply[C](bi: B => C): F[C] =
          r(bi compose g)
      }
    }
  }
}