def runWriter[W, A]: Writer[W, A] => (A, W) = {
  case Writer((a, w)) => (a, w)
}