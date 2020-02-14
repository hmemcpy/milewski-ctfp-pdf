(* Store is the comonad version of State *)
type ('s, 'a) store = Store of ('s -> 'a) * 's
