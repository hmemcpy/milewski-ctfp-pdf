module OpContravariant(T : sig type r end) : Contravariant = struct
  type 'a t = (T.r, 'a) op
  let contramap f h = fun b -> h (f b)
end
