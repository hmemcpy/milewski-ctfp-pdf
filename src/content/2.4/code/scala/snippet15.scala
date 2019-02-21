implicit val streamRepresentable = new Representable[Stream] {
  type Rep = Int

  def tabulate[X](f: Rep => X): Stream[X] = 
    Stream[X](() => f(0), () => tabulate(f compose (_ + 1)))

  def index[X]: Stream[X] => Rep => X = {
    case Stream(b, bs) => 
      n =>
        if (n == 0) b()
        else index(bs())(n - 1)
  }
}