module type NT_AX_FX = {
  type a;
  type t('x);
  
  let alpha: (a => 'x) => t('x);
};
