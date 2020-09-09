/* ReasonML doesn't have a built in Const type */
type const('a, 'b) =
  | Const('a);

/* ReasonML doesn't have a built in either type */
type either('a, 'b) =
  | Left('a)
  | Right('b);

/* Either type */
type option('a) = either(const(unit, 'a), id('a));
