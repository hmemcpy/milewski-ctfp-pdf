def fmapO[A, B]: (A => B) => Option[A] => Option[B] =
  optionFunctor.fmap
def fmapL[A, B]: (A => B) => List[A] => List[B] =
  listFunctor.fmap
def fmapC[A, B]: (A => B) => Option[List[A]] => Option[List[B]] =
  fmapO.compose(fmapL)

val mis2 = fmapC(square)(mis)