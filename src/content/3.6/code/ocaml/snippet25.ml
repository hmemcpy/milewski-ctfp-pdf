let uncurry f (a, b) = f a b

let join (ssa : ('s, ('s, 'a) state) state) : ('s, 'a) state =
  State (uncurry run_state % run_state ssa)
