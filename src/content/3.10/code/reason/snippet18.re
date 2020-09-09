module type Procompose = {
  type p('a, 'b);
  type q('a, 'b);

  type procompose(_, _) =
    | Procompose(q('a, 'c) => p('c, 'b)): procompose('a, 'b);
};
