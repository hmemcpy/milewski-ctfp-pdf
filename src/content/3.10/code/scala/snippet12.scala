def lambdaP[P[_, _]](P: Profunctor[P]): DiaProd[P] => ProdP[P] = {
  case DiaProd(paa) =>
    new ProdP[P] {
      def apply[A, B](f: A => B): P[A, B] =
        lambda(P)(paa[A])(f)
    }
}

def rhoP[P[_, _]](P: Profunctor[P]): DiaProd[P] => ProdP[P] = {
  case DiaProd(paa) =>
    new ProdP[P] {
      def apply[A, B](f: A => B): P[A, B] =
        rho(P)(paa[B])(f)
    }
}