module Kleisli (M : MonadJoin) = struct
  let ( >=> ) f g a = M.join (M.fmap g (f a))
end
