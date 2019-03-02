def lambda[P[- _, _]](P: Profunctor[P]): SumP[P] => DiagSum[P] =
  sump => new DiagSum[P] {
    def paa[A]: P[A, A] =
      P.dimap(sump.f)(identity[A])(sump.pab)
  }

def rho[P[_, _]](P: Profunctor[P]): SumP[P] => DiagSum[P] =
  sump => new DiagSum[P] {
    def paa[A]: P[A, A] =
      P.dimap(identity[A])(sump.f)(sump.pab)
  }