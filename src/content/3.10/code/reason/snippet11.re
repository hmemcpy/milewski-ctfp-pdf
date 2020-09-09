module type DiaProd = {
  type p('a, 'b);
  type diaprod('a) =
    | DiaProd(p('a, 'a));
};
