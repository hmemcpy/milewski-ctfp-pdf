module WriterMonadBind = (W: Monoid) => {
  let (>>=) = (Writer(a, w), f) => {
    let Writer(b, w') = f(a);
    Writer(b, W.mappend(w, w'));
  };
};
