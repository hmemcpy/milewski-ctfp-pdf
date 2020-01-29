module type Contravariant = sig
  type 'a t

  val contramap : ('b -> 'a) -> 'a t -> 'b t
end
