/** Deriving a functor in ReasonML is not available as a 
 * language extension. You could try experimental library 
 * like ocsigen to derive functors.*/
type tree('a) =
  | Leaf('a)
  | Node(tree('a), tree('a));
