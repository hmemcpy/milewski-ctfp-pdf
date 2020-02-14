module CoKleisliImpl = struct
type 'a w
let (=>=) : ('a w -> 'b) -> ('b w -> 'c) -> ('a w -> 'c) = fun f g ->
  g ...
end
