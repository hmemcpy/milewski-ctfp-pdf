val f : a -> b
val g : b -> c
val h : c -> d

h % (g % f) = (h % g) % f = h % g % f
