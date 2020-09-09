module type NT_ListX_IntX = {
  type a = int;
  type t('x) = list('x);
  
  let beta: (t('x), a) => 'x;
};
