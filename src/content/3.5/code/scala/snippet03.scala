// Streams in Scala can be
// thought of as lazy lists
def triples = for {
  z <- Stream.from(1)
  x <- 1 to z
  y <- x to z
  _ <- guard(x * x + y * y == z * z)
} yield (x, y, z)