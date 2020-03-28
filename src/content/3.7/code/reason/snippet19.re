let rec duplicate = (Cons(x, xs)) =>
  Cons(Cons(x, xs), Lazy.from_val(duplicate(Lazy.force(xs))));
