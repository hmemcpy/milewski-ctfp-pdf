module type Contravariant = {
  type t('a);
  
  let contramap: ('b => 'a, t('a)) => t('b);
};
