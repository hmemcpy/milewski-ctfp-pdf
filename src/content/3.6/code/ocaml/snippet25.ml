let join : ('s, ('s, 'a) state) state -> ('s, 'a) state =
 fun ssa -> State (uncurry run_state <.> run_state ssa)
;;
