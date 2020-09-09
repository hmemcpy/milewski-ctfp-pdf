module Test_Functor_Compose = (F: Functor) => {
  open F;

  /* Compose */
  let (<.>) = (f, g, x) => f(g(x));
  
  let test_compose = (f, g, x) =>
    assert(fmap(f <.> g, x) == fmap(f, fmap(g, x)));
};
