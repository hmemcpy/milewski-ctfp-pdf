module type Eq = {
  type a;
  
  let (===): (a, a) => bool;
};
