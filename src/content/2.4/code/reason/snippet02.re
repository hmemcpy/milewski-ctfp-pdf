module ReaderFunctor = (T: {type r;}) : Functor => {
  type t('a) = reader(T.r, 'a);
  
  let fmap = (f, h, a) => f(h(a));
};
