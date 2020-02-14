module type Chapter5_product_projection_example = functor
  (Product : Chapter5_Product)
  -> sig
  val m : Product.c -> Product.a * Product.b
end

module ProjectionImpl (Product : Chapter5_Product) = struct
  let m c = Product.p c, Product.q c
end
