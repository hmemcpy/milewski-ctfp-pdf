val process: String => Writer[List[String]] = {
  import kleisli._
  upCase >=> toWords
}