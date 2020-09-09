module type FreeMonoidRep = (F: Functor) => {
  type x;
  type m;
  
  let p: x => F.t(m);
};
