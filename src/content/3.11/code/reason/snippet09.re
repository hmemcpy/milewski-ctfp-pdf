module type FreeF = {
  type f('a);
  type a;
  type i;

  let h: i => a;
  let fi: i => f(i);
};
