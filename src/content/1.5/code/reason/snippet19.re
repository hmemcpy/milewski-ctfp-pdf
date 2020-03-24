module type Chapter5_product_projection_example =
  (Product: Chapter5_Product) => {
    let m: Product.c => (Product.a, Product.b);
};

module ProjectionImpl = (Product: Chapter5_Product) => {
  let m = c => (Product.p(c), Product.q(c));
};
