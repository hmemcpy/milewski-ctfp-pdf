module type Lan = {
  type k('a);
  type d('a);
  type a;
  type i;

  let fk: k(i) => a;
  let di: d(i);
};
