join :: State s (State s a) -> State s a
join ssa = State (uncurry runState . runState ssa)