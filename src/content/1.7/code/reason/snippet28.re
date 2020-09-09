module Const_Functor = (T: T) : Functor => {
  type t('a) = const(T.t, 'a);
  
  // or even let fmap = (_, c) => c;
  let fmap = (f, Const(c)) => Const(c); 
};
