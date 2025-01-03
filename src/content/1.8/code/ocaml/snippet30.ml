(* Writing the full implementation without deriving any of the functions *)
module ProfunctorArrow : Profunctor
with type ('a, 'b) t = 'a -> 'b = struct
  type ('a, 'b) t = 'a -> 'b

  let ( % ) = Fun.compose
  let dimap ab cd bc = cd % bc % ab
  let lmap f g = g % f
  let rmap f g = f % g
end
