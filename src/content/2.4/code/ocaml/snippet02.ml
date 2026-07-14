module ReaderFunctor (T : sig
  type r
end) : Functor with type 'a t = (T.r, 'a) reader = struct
  type 'a t = (T.r, 'a) reader

  let fmap f h a = f (h a)
end
