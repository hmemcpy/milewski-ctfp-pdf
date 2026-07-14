module Bifunctor_Product = Bifunctor_From_Bimap (struct
  type ('a, 'b) t = 'a * 'b

  let bimap f g (l, r) = (f l, g r)
end)
