module type Functor = sig
  type 'a t

  val fmap : ('a -> 'b) -> 'a t -> 'b t
end
