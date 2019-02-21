def ana[F[_], A](coalg: A => F[A])
                (implicit F: Functor[F]): A => Fix[F] =
  (Fix.apply[F] _).compose(F.fmap(ana(coalg)) _ compose coalg)