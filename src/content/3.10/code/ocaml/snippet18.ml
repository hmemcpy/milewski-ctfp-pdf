module type Procompose = sig
  type ('a, 'b) p
  type ('a, 'b) q

  type (_, _) procompose =
    | Procompose : (('a, 'c) q -> ('c, 'b) p) -> ('a, 'b) procompose
end
