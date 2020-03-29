module type DiagSum = {
  type a;
  type p('a, 'b);

  let paa: p(a, a);
};
