type state('s, 'a) =
  | State('s => ('a, 's));
