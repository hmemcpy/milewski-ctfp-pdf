module type CoKleisliExtend = sig
  type 'a w

  val extend : ('a w -> 'b) -> 'a w -> 'b w
end

module CoKleisliImpl (C : CoKleisliExtend) = struct
  type 'a w = 'a C.w

  let ( =>= ) : ('a w -> 'b) -> ('b w -> 'c) -> 'a w -> 'c =
   fun f g -> compose g (C.extend f)
 ;;
end
