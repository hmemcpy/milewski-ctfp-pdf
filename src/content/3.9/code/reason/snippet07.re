type store('s, 'a) =
  | Store('s => 'a, 's);
