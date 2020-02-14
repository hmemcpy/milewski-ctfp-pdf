module BiCompBifunctor
    (BF : BifunctorCore)
    (FU : Functor)
    (GU : Functor) : BifunctorCore = struct
  type ('a, 'b) t = BiComp of ('a FU.t, 'b GU.t) BF.t

  let bimap f g (BiComp x) =
    BiComp (BF.bimap (FU.fmap f) (GU.fmap g) x)
  ;;
end
