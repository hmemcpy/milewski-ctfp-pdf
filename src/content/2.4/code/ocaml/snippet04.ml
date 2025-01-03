module OpContravariant (T : sig
  type r
end) : Contravariant with type 'a t = (T.r, 'a) op = struct
  type 'a t = (T.r, 'a) op

  let contramap f h b = h (f b)
end
