def bimap: (FU[A] => FU[A1]) =>
    (GU[B] => GU[B1]) =>
    BiComp[BF, FU, GU, A, B] =>
    BiComp[BF, FU, GU, A1, B1]