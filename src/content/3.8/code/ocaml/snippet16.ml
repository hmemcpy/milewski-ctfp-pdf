module Cata (F : Functor) = struct
  type 'a fix = Fix of 'a fix F.t

  let fix : 'a fix F.t -> 'a fix = fun f -> Fix f
  let unfix : 'a fix -> 'a fix F.t = fun (Fix f) -> f

  let rec cata : ('a F.t -> 'a) -> 'a fix -> 'a =
   fun alg fixf -> alg (F.fmap (cata alg) (unfix fixf))
 ;;
end
