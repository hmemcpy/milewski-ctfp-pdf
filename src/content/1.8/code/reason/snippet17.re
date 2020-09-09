module KleisliComposition = {
  let (>=>): ('a => writer('b), 'b => writer('c), 'a) => writer('c) =
    (m1, m2, x) => {
      let (y, s1) = m1(x);
      let (z, s2) = m2(y);
      (z, StringLabels.concat(~sep="", [s1, s2]));
    };
};
