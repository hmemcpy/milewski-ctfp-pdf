module Ana (F : Functor) (Fix : Fixpoint with type 'a funct = 'a F.t) =
struct
  let rec ana (coalg : 'a -> 'a F.t) (a : 'a) : 'a Fix.t =
    Fix.Fix (F.fmap (fun x -> ana coalg x) (coalg a))
end
