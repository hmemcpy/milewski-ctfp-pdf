type maybe('a) =
  | Nothing
  | Just('a);
  
let maybe_tail =
  fun
  | Nil => Nothing
  | Cons(_, xs) => Just(xs);
