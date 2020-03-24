let dumb: 'a. reader(unit, 'a) => option('a) =
  fun
  | Reader(_) => None;
