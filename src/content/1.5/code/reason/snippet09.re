module type Chapter5_Product = {
  type a;
  type c;
  type b;
  
  let p: c => a;
  let q: c => b;
};
