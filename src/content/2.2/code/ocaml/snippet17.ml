type 'a tostring = ToString of ('a -> string)

module ToStringInstance : Contravariant with type 'a t = 'a tostring = struct
  type 'a t = 'a tostring

  let contramap f (ToString g) = ToString (Fun.compose g f)
end
