let contramap (f : 'b -> 'a) (g : ('r, 'a) op) : ('r, 'b) op =
  Fun.flip Fun.compose f g
