module type Lst = {
  type a;
  type m;

  module M: Monoid with type m = m;

  type lst = (a => M.m) => M.m;

  let f: lst;
};
