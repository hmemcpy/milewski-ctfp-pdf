module Fix = (F: Functor) => {
  type fix('a) =
    | Fix(F.t(fix('a)));

  let fix: F.t(fix('a)) => fix('a) = (
    f => Fix(f): F.t(fix('a)) => fix('a)
  );
};
