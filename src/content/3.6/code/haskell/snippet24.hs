ssa :: State s (State s a)
runState ssa :: s -> (State s a, s)