module type ProdP = {
  type p('a, 'b);
  type prod_p('a, 'b) = ('a => 'b) => p('a, 'b);
};
