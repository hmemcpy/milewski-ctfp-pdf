module Kleisli_Composition
    (T : Monad_Join)
    (F : Functor with type 'a t = 'a T.t) =
struct
  let ( % ) = Fun.compose
  let h g f = T.join % F.fmap g % f
end
