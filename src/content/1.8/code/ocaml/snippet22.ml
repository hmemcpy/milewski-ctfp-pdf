module ReaderFunctor (In : sig
  type r
end) : Functor = struct
  type 'a t = (In.r, 'a) reader

  let fmap f g = compose f g
end
