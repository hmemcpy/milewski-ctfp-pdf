module type AtoB = {
  type a;
  type b;
  
  let f: a => b;
};
