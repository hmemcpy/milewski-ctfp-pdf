module type NT_FX_AX = {
  type a;
  type t('x);
  
  let beta: (t('x), a) => 'x;
};
