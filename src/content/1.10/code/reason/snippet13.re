let un_const: 'c 'a. const('c, 'a) => 'c =
  fun
  | Const(c) => c;
