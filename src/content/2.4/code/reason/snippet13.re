module type Representable = {
  type t('x);
  type rep; /* Representing type 'a' */
  
  let tabulate: (rep => 'x) => t('x);
  let index: (t('x), rep) => 'x;
};
