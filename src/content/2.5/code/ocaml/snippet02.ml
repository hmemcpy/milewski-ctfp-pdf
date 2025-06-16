module ReaderFunctor (T : sig
  type a
end) : Functor with type 'x t = (T.a, 'x) reader = struct
  type 'x t = (T.a, 'x) reader

  let fmap (f : 'x -> 'y) (r : 'x t) : 'y t = Fun.compose f r
end
