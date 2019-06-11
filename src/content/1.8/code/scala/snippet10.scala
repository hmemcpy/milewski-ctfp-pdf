implicit def bicompBiFunctor[
    BF[_, _], FU[_], GU[_]](
    implicit BF: Bifunctor[BF],
    FU: Functor[FU], GU: Functor[GU]) = {
  // partially-applied type BiComp
  type BiCompAB[A, B] = BiComp[BF, FU, GU, A, B]
  new Bifunctor[BiCompAB] {
    override def bimap[A, B, C, D](f1: A => C)(f2: B => D): BiCompAB[A, B] => BiCompAB[C, D] = {
      case BiComp(x) =>
        BiComp(
          BF.bimap(FU.fmap(f1))(GU.fmap(f2))(x)
        )
    }
  }
}