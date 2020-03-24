module type Monoid = {
  type m;
  
  let mempty: m;
  let mappend: (m, m) => m;
};
