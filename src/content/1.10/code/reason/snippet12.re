/* ReasonML requires mutually recursive functions 
* to be defined together */
let rec length: list('a) => const(int, 'a) = (
  fun
  | [] => Const(0)
  | [_, ...xs] => Const(1 + un_const(length(xs))):
    list('a) => const(int, 'a)
)
and un_const: 'c 'a. const('c, 'a) => 'c =
  fun
  | Const(c) => c;
