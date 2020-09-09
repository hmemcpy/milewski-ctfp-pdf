module WriterMonad = (W: Monoid) : Monad_Bind => {
  type m('a) = writer(W.t, 'a);

  let return = a => Writer(a, W.mempty);

  let (>>=) = (Writer(a, w), k) => {
    let (a', w') = run_writer(k(a));
    Writer(a', W.mappend(w, w'));
  };
};
