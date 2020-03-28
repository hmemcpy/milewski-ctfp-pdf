module type CoKleisliExtend = {
  type w('a);

  let extend: (w('a) => 'b, w('a)) => w('b);
};

module CoKleisliImpl = (C: CoKleisliExtend) => {
  type w('a) = C.w('a);

  let (=>=): (w('a) => 'b, w('b) => 'c, w('a)) => 'c = (
    (f, g) => compose(g, C.extend(f)):
      (w('a) => 'b, w('b) => 'c, w('a)) => 'c
  );
};
