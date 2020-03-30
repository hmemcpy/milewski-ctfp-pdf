let fold_map = (type i, module M: Monoid with type m = i, xs, f) =>
  List.fold_left((acc, a) => M.mappend(acc, f(a)), M.mempty, xs);

let to_lst = (type x, xs: list(x)) => {
  module LM: Monoid with type m = list(x) = 
    ListMonoid({type a = x;});

  (module {
      type a = x;
      type m = list(x);

      module M = LM;

      type lst = (a => LM.m) => LM.m;

      let f = g => fold_map((module LM), xs, g);
  });
};

let from_lst = (type x, 
    module LstImpl: Lst with type a = x and type m = list(x)
  ) => LstImpl.f(x => [x]);
