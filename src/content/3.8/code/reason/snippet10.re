module Fix = (F: Functor) => {
  type fix('a) =
    | Fix(F.t(fix('a)));
};
