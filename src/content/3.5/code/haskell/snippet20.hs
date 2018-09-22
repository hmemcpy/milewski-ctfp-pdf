get :: State s s
get = State (\s -> (s, s))