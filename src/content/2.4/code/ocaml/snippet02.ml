module ReaderFunctor(T : sig type r end) : Functor = struct
  type 'a t = (T.r, 'a) reader
  let fmap f h = fun a -> f (h a)
end
