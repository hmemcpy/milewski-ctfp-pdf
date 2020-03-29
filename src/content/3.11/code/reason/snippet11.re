module type FreeF_Alt = {
  type a;
  type f('a);

  let freeF: (a => 'i) => f('i);
};
