/* OCaml library `gen` provides useful helpers for
   potentially infinite iterators. You can install it
   with `opam install gen`. To use it in the toplevel,
   you need to `#require "gen"` */
let era: Gen.t(int) => stream_f(int, Gen.t(int)) = (ilist => {
    let notdiv = (p, n) => n mod p !== 0;
    let p = Gen.get_exn(ilist);
    StreamF(p, Gen.filter(notdiv(p), ilist));
});