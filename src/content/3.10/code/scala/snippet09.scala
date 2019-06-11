def lambda[A, B, P[_, _]](P: Profunctor[P]): P[A, A] => (A => B) => P[A, B] =
  paa => f => P.dimap(identity[A])(f)(paa)

def rho[A, B, P[_, _]](P: Profunctor[P]): P[B, B] => (A => B) => P[A, B] =
  pbb => f => P.dimap(f)(identity[B])(pbb)