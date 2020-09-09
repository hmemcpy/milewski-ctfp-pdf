module Identity_Functor: Functor = {
  type t('a) = id('a);
  
  let fmap = (f, Id(a)) => Id(f(a));
};
