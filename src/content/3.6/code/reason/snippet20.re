type reader('s, 'a) =
  | Reader('s => 'a);
