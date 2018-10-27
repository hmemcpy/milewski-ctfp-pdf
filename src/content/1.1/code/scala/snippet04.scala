val f: A => B
val g: B => C
val h: C => D

h compose (g compose f) === (h compose g) compose f === h compose g compose f