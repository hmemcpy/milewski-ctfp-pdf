module OpContravariant (T : sig
  type r
end) : Contravariant = struct
  type 'a t = (T.r, 'a) op

  let contramap f h b = h (f b)
end
