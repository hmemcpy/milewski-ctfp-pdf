module Fix = (F: Functor) => {
  type fix('a) =
    | In(F.t(fix('a)));
};
