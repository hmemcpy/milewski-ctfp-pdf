module Kleisli (M : Monad_Join)
    (F : Functor with type 'a t = 'a M.t) = struct
  let ( >=> ) f g a = M.join (F.fmap g (f a))
end
