module type Functor = sig
  type 'a t

  val fmap : ('a -> 'b) -> 'a t -> 'b t
end

module type Profunctor = sig
  type ('a, 'b) p

  val dimap : ('c -> 'a) -> ('b -> 'd) -> ('a, 'b) p -> ('c, 'd) p
end

let id a = a
