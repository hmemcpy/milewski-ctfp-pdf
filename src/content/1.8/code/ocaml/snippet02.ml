module Bifunctor_Product : BifunctorCore = struct
  type ('a, 'b) t = 'a * 'b

  let bimap f g (l, r) = f l, g r
end
