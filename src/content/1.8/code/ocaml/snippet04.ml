type ('a, 'b) either =
  | Left of 'a
  | Right of 'b

module Bifunctor_Either : BifunctorCore = struct
  type ('a, 'b) t = ('a, 'b) either

  let bimap f g = function
    | Left a -> Left (f a)
    | Right b -> Right (g b)
  ;;
end
