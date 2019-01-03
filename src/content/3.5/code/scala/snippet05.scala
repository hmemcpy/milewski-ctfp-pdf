def triples = for {
  z <- Stream.from(1)
  x <- 1 to z
  y <- x to z
  if x * x + y * y == z * z
} yield (x, y, z)