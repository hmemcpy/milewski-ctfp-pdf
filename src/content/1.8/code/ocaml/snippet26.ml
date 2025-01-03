module OpContravariant (In : sig
  type r
end) : Contravariant with type 'a t = (In.r, 'a) op = struct
  type 'a t = (In.r, 'a) op

  let contramap f g = Fun.compose g f
end
