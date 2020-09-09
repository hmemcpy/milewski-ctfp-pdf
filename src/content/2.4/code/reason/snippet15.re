module StreamRepresentable: Representable = {
  type rep = int;
  type t('x) = stream('x);

  let rec tabulate = f => Cons(f(0), lazy(tabulate(compose(f, succ))));

  let rec index = (Cons(b, bs), n) =>
    n == 0 ? b : index(Lazy.force(bs), n - 1);
};
