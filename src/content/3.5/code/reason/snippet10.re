let (>>=) = (ra, k) => Reader(e => {
  let a = run_reader(ra, e);
  let rb = k(a);
  ...
});