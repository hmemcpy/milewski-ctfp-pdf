module type Maybe_Functor = {
  type a;
  type b;
  
  let fmap: (a => b, option(a)) => option(b);
};
