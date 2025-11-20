module Bifunctor_Either = Bifunctor_From_Bimap (struct
  open Either

  type ('a, 'b) t = ('a, 'b) Either.t

  let bimap f g = function
    | Left a -> Left (f a)
    | Right b -> Right (g b)
end)
