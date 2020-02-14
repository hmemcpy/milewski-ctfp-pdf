module OpContravariant (In : sig
  type r
end) : Contravariant = struct
  type 'a t = (In.r, 'a) op

  let contramap f g = compose g f
end
