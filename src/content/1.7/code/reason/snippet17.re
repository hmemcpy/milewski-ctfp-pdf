module type List_Functor_Type = {
  type t('a) = list('a);
  
  let fmap: ('a => 'b, list('a)) => list('b);
};
