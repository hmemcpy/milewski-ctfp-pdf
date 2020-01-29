module Chapter5_Product_Example2 : Chapter5_Product = struct
  type a = int
  type b = bool
  type c = int * int * bool

  let p (x, _, _) = x
  let q (_, _, b) = b
end
