module ListMonoid (T1 : sig
  type a
end) : Monoid with type m = T1.a list = struct
  type m = T1.a list

  let mempty = []
  let mappend xs ys = List.append xs ys
end
