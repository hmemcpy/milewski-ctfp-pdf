type either('a, 'b) =
  | Left('a)
  | Right('b);

module Bifunctor_Either: BifunctorCore = {
  type t('a, 'b) = either('a, 'b);
  
  let bimap = (f, g) =>
    fun
    | Left(a) => Left(f(a))
    | Right(b) => Right(g(b));
};
