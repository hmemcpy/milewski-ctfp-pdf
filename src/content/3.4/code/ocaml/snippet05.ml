module WriterMonad (W : Monoid) :
  Monad with type 'a m = (W.a, 'a) writer = struct
  type 'a m = (W.a, 'a) writer

  let ( >=> ) f g a =
    let (Writer (b, w)) = f a in
    let (Writer (c, w')) = g b in
    Writer (c, W.mappend w w')


  let return a = Writer (a, W.mempty)
end
