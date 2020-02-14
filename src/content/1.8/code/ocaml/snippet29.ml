(* Profunctor definition *)
module type Profunctor = sig
  type ('a, 'b) p

  val dimap : ('a -> 'b) -> ('c -> 'd) -> ('b, 'c) p -> ('a, 'd) p
end

(* Profunctor alternate definition *)
module type ProfunctorExt = sig
  type ('a, 'b) p

  val lmap : ('a -> 'b) -> ('b, 'c) p -> ('a, 'c) p
  val rmap : ('b -> 'c) -> ('a, 'b) p -> ('a, 'c) p
end

(* Profunctor dimap defined using lmap and rmap *)
module Profunctor_Using_Ext (PF : ProfunctorExt) : Profunctor = struct
  type ('a, 'b) p = ('a, 'b) PF.p

  let dimap f g = compose (PF.lmap f) (PF.rmap g)
end

(** Profunctor lmap and rmap defined using dimap *)
module ProfunctorExt_Using_Dimap (PF : Profunctor) : ProfunctorExt =
struct
  type ('a, 'b) p = ('a, 'b) PF.p

  let lmap f = PF.dimap f id
  let rmap g = PF.dimap id g
end
