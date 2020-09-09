module Fix = (F: Functor) => {
  type fix('a) =
    | Fix(F.t(fix('a)));

  let unfix: fix('a) => F.t(fix('a)) = (
    (Fix(f)) => f: fix('a) => F.t(fix('a))
  );
};
