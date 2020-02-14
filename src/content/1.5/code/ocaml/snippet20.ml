module type Factorizer = functor (Product : Chapter5_Product) -> sig
  val factorizer
    :  (Product.c -> Product.a)
    -> (Product.c -> Product.b)
    -> Product.c
    -> Product.a * Product.b
end

module FactorizerImpl (Product : Chapter5_Product) = struct
  let factorizer ca cb = Product.p ca, Product.q cb
end
