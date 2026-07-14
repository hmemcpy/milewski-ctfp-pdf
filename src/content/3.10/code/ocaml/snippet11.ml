module type DiaProd = sig
  type ('a, 'b) t
  type 'a diaprod = DiaProd of ('a, 'a) t
end
