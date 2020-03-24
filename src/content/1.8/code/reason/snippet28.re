let contramap: ('b => 'a, op('r, 'a)) => op('r, 'b) = (
  (f, g) => flip(compose, f, g): ('b => 'a, op('r, 'a)) => op('r, 'b)
);
