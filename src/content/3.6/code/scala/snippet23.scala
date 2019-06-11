def runState[S, A]: State[S, A] => S => (A, S) = {
  case State(f) => s => f(s)
}