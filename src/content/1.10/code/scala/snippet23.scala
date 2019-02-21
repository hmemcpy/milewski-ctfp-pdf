def predToStr[A]: Op[Boolean, A] => Op[String, A] = {
  case Op(f) => Op(x => if (f(x)) "T" else "F")
}