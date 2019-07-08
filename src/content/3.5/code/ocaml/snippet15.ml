module WriterMonad (W : Monoid) : Monad_Bind = struct
  type 'a m = (W.t, 'a) writer

  let return a = Writer (a, W.mempty)

  let ( >>= ) (Writer (a, w)) k =
    let a', w' = run_writer (k a) in
    Writer (a', W.mappend w w')
end
