instance
  constFunc : Functor (Const c)
  constFunc .fmap _ (mkConst c) = mkConst c
