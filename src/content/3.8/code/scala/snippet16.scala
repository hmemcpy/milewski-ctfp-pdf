def cata[F[_], A](alg: F[A] => A)
                 (implicit F: Functor[F]): Fix[F] => A =
  alg.compose(F.fmap(cata(alg)) _ compose unFix)