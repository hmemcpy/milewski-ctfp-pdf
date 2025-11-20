module type Bifunctor = sig
  type ('a, 'b) t

  val bimap : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) t -> ('c, 'd) t
  val first : ('a -> 'c) -> ('a, 'b) t -> ('c, 'b) t
  val second : ('b -> 'd) -> ('a, 'b) t -> ('a, 'd) t
end

(** You can represent a bifunctor in one of the two forms and
    derive one from the other. *)
module type Bimap = sig
  type ('a, 'b) t

  val bimap : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) t -> ('c, 'd) t
end

module type Fmaps = sig
  type ('a, 'b) t

  val first : ('a -> 'c) -> ('a, 'b) t -> ('c, 'b) t
  val second : ('b -> 'd) -> ('a, 'b) t -> ('a, 'd) t
end

module Bifunctor_From_Bimap (M : Bimap) :
  Bifunctor with type ('a, 'b) t = ('a, 'b) M.t = struct
  include M

  let first g x = M.bimap g Fun.id x
  let second h x = M.bimap Fun.id h x
end

module Bifunctor_From_Fmaps (M : Fmaps) :
  Bifunctor with type ('a, 'b) t = ('a, 'b) M.t = struct
  include M

  let bimap g h x = M.first g (M.second h x)
end
