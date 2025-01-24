module ListMonoid (T1 : sig
  type a
end) : Monoid with type t = T1.a list = struct
  type t = T1.a list

  let mempty = []
  let mappend xs ys = xs @ ys
end
