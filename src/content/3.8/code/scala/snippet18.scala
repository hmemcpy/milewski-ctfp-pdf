def fib: NatF[(Int, Int)] => (Int, Int) = {
  case ZeroF => (1, 1)
  case SuccF((m, n)) => (n, m + n)
}