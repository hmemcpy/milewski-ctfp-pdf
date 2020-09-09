module Kleisli = (M: MonadJoin) => {
  let (>=>) = (f, g, a) => M.join(M.fmap(g, f(a)));
};
