module type CoKleisli = {
  type w('a);

  let (=>=): (w('a) => 'b, w('b) => 'c, w('a)) => 'c;
};
