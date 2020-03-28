let (=>=) = (f, g, P(e, a)) => {
  let b = f(P(e, a));
  let c = g(P(e, b));
  c;
};
