let obvious: 'a. reader(unit, 'a) => option('a) =
  fun
  | Reader(f) => Some(f());
