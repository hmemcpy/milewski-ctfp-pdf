(* Assuming these signatures *)
val f : a -> b
val g : b -> c
val h : c -> d
(* These are equivalent *)
h % (g % f) = (h % g) % f = h % g % f
