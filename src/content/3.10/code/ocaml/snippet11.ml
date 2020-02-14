module type DiaProd = sig
  type ('a, 'b) p
  type 'a diaprod = DiaProd of ('a, 'a) p
end
