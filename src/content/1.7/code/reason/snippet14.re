module type Functor = {
  type t('a);
  
  let fmap: ('a => 'b, t('a)) => t('b);
};
