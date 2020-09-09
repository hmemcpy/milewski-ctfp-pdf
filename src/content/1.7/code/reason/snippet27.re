module type Const_Functor_Example = {
  let fmap: ('a => 'b, const('c, 'a)) => const('c, 'b);
};
