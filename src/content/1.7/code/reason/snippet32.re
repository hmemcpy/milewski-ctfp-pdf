module type Fmap_Alt_Sig_Example = {
  type t('a);
  
  let fmap: ('a => 'b, t('a)) => t('b);
};
