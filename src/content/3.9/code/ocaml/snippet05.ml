module Kleisli_Composition (T : MonadJoin) = struct
  let h g f = T.join <.> T.fmap g <.> f
end
