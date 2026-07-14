module Kleisli (M : Monad_Join) = struct
  let ( % ) = Fun.compose
  let ( >=> ) f g = M.join % M.fmap g % f
end
