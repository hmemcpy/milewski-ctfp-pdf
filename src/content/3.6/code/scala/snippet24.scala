def ssa[S, A]: State[S, State[S, A]]

def rss[S, A]: S => (State[S, A], S) =
  runState[S, State[S, A]](ssa)