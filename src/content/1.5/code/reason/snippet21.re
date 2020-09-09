module type CoProduct = {
  type a;
  type b;
  type c;
  
  let i: a => c;
  let j: b => c;
};
