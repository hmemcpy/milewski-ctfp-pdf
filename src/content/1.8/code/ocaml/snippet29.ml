module type Profunctor = sig
  type ('a, 'b) t

  val dimap : ('a -> 'b) -> ('c -> 'd) -> ('b, 'c) t -> ('a, 'd) t
  val lmap : ('a -> 'b) -> ('b, 'c) t -> ('a, 'c) t
  val rmap : ('b -> 'c) -> ('a, 'b) t -> ('a, 'c) t
end

(* Like with the bifunctor, we can represent a profunctor in
   one of the two forms and derive one from the other. *)
module type Dimap = sig
  type ('a, 'b) t

  val dimap : ('a -> 'b) -> ('c -> 'd) -> ('b, 'c) t -> ('a, 'd) t
end

module type Maps = sig
  type ('a, 'b) t

  val lmap : ('a -> 'b) -> ('b, 'c) t -> ('a, 'c) t
  val rmap : ('b -> 'c) -> ('a, 'b) t -> ('a, 'c) t
end

module Profunctor_From_Dimap (M : Dimap) :
  Profunctor with type ('a, 'b) t = ('a, 'b) M.t = struct
  include M

  let lmap f = M.dimap f Fun.id
  let rmap g = M.dimap Fun.id g
end

module Profunctor_From_Maps (M : Maps) :
  Profunctor with type ('a, 'b) t = ('a, 'b) M.t = struct
  include M

  let dimap f g = Fun.compose (M.lmap f) (M.rmap g)
end
