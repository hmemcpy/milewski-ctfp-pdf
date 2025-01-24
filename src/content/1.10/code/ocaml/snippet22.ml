module Op_Contravariant (T : sig
  type r
end) : Contravariant with type 'a t = (T.r, 'a) op = struct
  type 'a t = (T.r, 'a) op

  let contramap f (Op g) = Op (Fun.compose g f)
end
