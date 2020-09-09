module type Monoid = {
  type m;

  let mappend: (m, m) => m;
  let mempty: m;
};
