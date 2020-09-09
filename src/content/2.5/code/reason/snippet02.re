module ReaderFunctor = (T: {type a;}) : Functor => {
  type t('x) = reader(T.a, 'x);
  
  let fmap: ('x => 'y, t('x)) => t('y) = (
    (f, r, a) => f(r(a)): ('x => 'y, t('x)) => t('y)
  );
};
