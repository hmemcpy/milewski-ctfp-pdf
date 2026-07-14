module WriterMonad (W : Monoid) : Monad_Bind
with type 'a t = (W.t, 'a) writer =
struct
  type 'a t = (W.t, 'a) writer

  let ( >>= ) (Writer (a, w)) k =
    let a', w' = run_writer (k a) in
    Writer (a', W.mappend w w')

  let return a = Writer (a, W.mempty)
end
