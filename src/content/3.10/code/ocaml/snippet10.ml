module type ProdP = sig
  type ('a, 'b) p
  type ('a, 'b) prod_p = ('a -> 'b) -> ('a, 'b) p
end
