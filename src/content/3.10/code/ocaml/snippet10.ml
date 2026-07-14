module type ProdP = sig
  type ('a, 'b) t
  type ('a, 'b) prod_p = ('a -> 'b) -> ('a, 'b) t
end
