let (>>=) = (sa, k) => State(s => {
  let (a, s') = run_state(sa, s);
  let sb = k(a);
  run_state(sb, s');
});
