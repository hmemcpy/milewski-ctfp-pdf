module WriterMonad = (W: Monoid) : 
    (Monad with type m('a) = writer(W.a, 'a)) => {
  type m('a) = writer(W.a, 'a);

  let (>=>) = (f, g, a) => {
    let Writer(b, w) = f(a);
    let Writer(c, w') = g(b);
    Writer(c, W.mappend(w, w'));
  };

  let return = a => Writer(a, W.mempty);
};
