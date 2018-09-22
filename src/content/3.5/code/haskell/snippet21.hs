put :: s -> State s ()
put s' = State (\s -> ((), s'))