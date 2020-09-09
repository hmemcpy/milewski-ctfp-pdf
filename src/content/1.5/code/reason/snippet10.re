module Chapter5_Product_Example:
  Chapter5_Product 
    with type a = int
    and type b = bool
    and type c = int = {
  type a = int;
  type b = bool;
  type c = int;

  let p = x => x;
  let q = _ => true;
};
