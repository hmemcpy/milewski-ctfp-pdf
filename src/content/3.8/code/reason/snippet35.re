/* Store is the comonad version of State */
type store('s, 'a) =
  | Store('s => 'a, 's);
