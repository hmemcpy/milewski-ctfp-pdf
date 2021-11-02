(** You can represent bifunctor defintion in two forms and implement
    just and derive the other from it. *)
module type BifunctorCore = sig
  type ('a, 'b) t

  val bimap : ('a -> 'c) -> ('b -> 'd) -> ('a, 'b) t -> ('c, 'd) t
end

module type BifunctorExt = sig
  type ('a, 'b) t

  val first : ('a -> 'c) -> ('a, 'b) t -> ('c, 'b) t
  val second : ('b -> 'd) -> ('a, 'b) t -> ('a, 'd) t
end

module BifunctorCore_Using_Ext (M : BifunctorExt) : BifunctorCore =
struct
  type ('a, 'b) t = ('a, 'b) M.t

  let bimap g h x = M.first g (M.second h x)
end

module BifunctorExt_Using_Core (M : BifunctorCore) : BifunctorExt =
struct
  type ('a, 'b) t = ('a, 'b) M.t

  let first g x = M.bimap g id x
  let second h x = M.bimap id h x
end
