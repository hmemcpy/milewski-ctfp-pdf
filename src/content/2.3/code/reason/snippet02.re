module ListMonoid = (T1: {type a;}) : 
    (Monoid with type m = list(T1.a)) => {
  type m = list(T1.a);

  let mempty = [];
  let mappend = (xs, ys) => List.append(xs, ys);
};
