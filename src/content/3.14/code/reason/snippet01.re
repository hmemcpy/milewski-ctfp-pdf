type either('a, 'b) =
  | Left('a)
  | Right('b);

type two = either(unit, unit);
