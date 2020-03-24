module type Factorizer = (Product: Chapter5_Product) => {
  let factorizer:
    (Product.c => Product.a, Product.c => Product.b, Product.c) =>
    (Product.a, Product.b);
};

module FactorizerImpl = (Product: Chapter5_Product) => {
  let factorizer = (ca, cb) => (Product.p(ca), Product.q(cb));
};
