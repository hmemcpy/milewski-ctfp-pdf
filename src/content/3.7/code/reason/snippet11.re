module CoKleisliImpl = {
  type w('a);
  let (=>=): (w('a) => 'b, w('b) => 'c, w('a)) => 'c = (f, g) =>
    g ... 
};
