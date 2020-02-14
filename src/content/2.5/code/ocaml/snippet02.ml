module ReaderFunctor (T : sig
  type a
end) : Functor = struct
  type 'x t = (T.a, 'x) reader

  let fmap : ('x -> 'y) -> 'x t -> 'y t = fun f r a -> f (r a)
end
