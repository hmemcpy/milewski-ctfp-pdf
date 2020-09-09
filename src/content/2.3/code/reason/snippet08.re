module type FreeMonoidRep = (F: Functor) => {
  type x;
  type n;
  
  let q: x => F.t(n);
};
