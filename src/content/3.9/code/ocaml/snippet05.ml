module Kleisli_Composition (T : Monad) = struct
  let h = T.join <.> T.fmap g <.> f
end
