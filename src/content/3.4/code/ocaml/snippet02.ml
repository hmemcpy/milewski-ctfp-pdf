module WriterInstance (W : sig
  type w
end) : Functor with type 'a t = (W.w, 'a) writer = struct
  type 'a t = (W.w, 'a) writer

  let fmap f (Writer (a, w)) = Writer (f a, w)
end
