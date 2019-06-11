runState :: State s a -> s -> (a, s)
runState (State f) s = f s