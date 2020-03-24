module StringMonoid: Monoid = {
  type a = string;
  
  let mempty = "";
  let mappend = (++);
};
