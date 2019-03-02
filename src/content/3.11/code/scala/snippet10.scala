implicit def freeFunctor[F[_]] = new Functor[FreeF[F, ?]] {
  def fmap[A, B](g: A => B)(fa: FreeF[F, A]): FreeF[F, B] = {
    new FreeF[F, B] {
      def h[I]: I => B = g compose fa.h
      def fi[I]: F[I] = fi
    }
  }
}