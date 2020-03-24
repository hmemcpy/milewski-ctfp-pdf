module Const_Functor = (T: T) : Functor => {
  type t('a) = const(T.t, 'a);
  
  let fmap = (f, Const(c)) => Const(c); /* or even let fmap = (_ c) => c */
};
