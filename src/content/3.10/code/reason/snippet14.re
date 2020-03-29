module Coend = (P: Profunctor) => {
  type coend =
    | Coend({c: 'a. P.p('a, 'a)});
};
