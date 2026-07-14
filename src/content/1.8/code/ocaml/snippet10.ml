module BiCompBifunctor (BF : Bifunctor) (FU : Functor) (GU : Functor) =
Bifunctor_From_Bimap (struct
  type ('a, 'b) t = ('a FU.t, 'b GU.t) BF.t

  let bimap f g x = BF.bimap (FU.fmap f) (GU.fmap g) x
end)
