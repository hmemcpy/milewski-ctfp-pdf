module ReaderFunctor (In : sig
  type r
end) : Functor with type 'a t = (In.r, 'a) reader = struct
  type 'a t = (In.r, 'a) reader

  let fmap f g = Fun.compose f g
end
