module WriterMonadBind (W : Monoid) = struct
  let ( >>= ) (Writer (a, w)) f =
    let (Writer (b, w')) = f a in
    Writer (b, W.mappend w w')
end
