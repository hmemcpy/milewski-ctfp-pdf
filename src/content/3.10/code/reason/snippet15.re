module type SumP = {
  type a;
  type b;
  type p('a, 'b);

  let f: b => a;
  let pab: p(a, b);
};
