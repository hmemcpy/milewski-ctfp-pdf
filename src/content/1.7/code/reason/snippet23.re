module Reader_Functor = (T: T) : Functor => {
  type t('a) = T.t => 'a;
  
  let fmap = (f, ra, r) => f(ra(r));
};
