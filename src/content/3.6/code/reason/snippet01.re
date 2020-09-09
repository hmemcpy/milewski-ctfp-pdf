module Kleisli = (M: MonadJoin) => {
  /* compose */
  let (<.>) = (f, g, x) => f(g(x));
  let (>=>) = (f, g) => M.join <.> M.fmap(g) <.> f;
};
