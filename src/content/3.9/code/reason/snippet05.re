module Kleisli_Composition = (T: MonadJoin) => {
  let h = (g, f) => T.join <.> T.fmap(g) <.> f;
};
