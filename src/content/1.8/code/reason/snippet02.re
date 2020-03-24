module Bifunctor_Product: BifunctorCore = {
  type t('a, 'b) = ('a, 'b);
  
  let bimap = (f, g, (l, r)) => (f(l), g(r));
};
