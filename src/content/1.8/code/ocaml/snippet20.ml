module PartialArrow (T : sig
  type r
end) =
struct
  type 'a t = T.r -> 'a
end
