module Cata (F : Functor) (Fix : Fixpoint with type 'a funct = 'a F.t) = struct
  let rec cata (alg : 'a F.t -> 'a) (fixf : 'a Fix.t) : 'a =
    alg (F.fmap (cata alg) (Fix.unfix fixf))
end
