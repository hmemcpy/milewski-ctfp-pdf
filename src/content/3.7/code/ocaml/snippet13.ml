module type CoKleisliExtend = sig
  type 'a w

  val extend : ('a w -> 'b) -> 'a w -> 'b w
end

module CoKleisliImpl (C : CoKleisliExtend) = struct
  type 'a w = 'a C.w

  let ( =>= ) (f : 'a w -> 'b) (g : 'b w -> 'c) : 'a w -> 'c =
    Fun.compose g (C.extend f)
end
