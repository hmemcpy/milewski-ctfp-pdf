module type Profunctor = sig
  type ('a, 'b) t

  val dimap : ('c -> 'a) -> ('b -> 'd) -> ('a, 'b) t -> ('c, 'd) t
end
