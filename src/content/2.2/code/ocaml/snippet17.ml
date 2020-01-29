module type Contravariant = sig
  type 'a t

  val contramap : ('b -> 'a) -> 'a t -> 'b t
end

type 'a tostring = ToString of ('a -> string)

module ToStringInstance : Contravariant = struct
  type 'a t = 'a tostring

  let contramap f (ToString g) = ToString (compose g f)
end
