module type Monoid = {
  type a;
  
  let mempty: a;
  let mappend: (a, a) => a;
};
