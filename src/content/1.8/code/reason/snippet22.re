module ReaderFunctor = (In: {type r;}) : Functor => {
  type t('a) = reader(In.r, 'a);
  
  let fmap = (f, g) => compose(f, g);
};
