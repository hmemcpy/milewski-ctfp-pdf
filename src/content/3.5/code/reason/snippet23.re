type cont('r, 'a) =
  | Cont(('a => 'r) => 'r);
