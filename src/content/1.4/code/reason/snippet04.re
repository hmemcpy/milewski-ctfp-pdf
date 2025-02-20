let (>=>) = (m1, m2) => {
  let (y, s1) = m1(x);

  let (z, s2) = m2(x);

  (z, StringLabels.concat(~sep="", [s1, s2]));
};
