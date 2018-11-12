def toListC[E]: Fix[StreamF[E, ?]] => List[E] = {
  def al: StreamF[E, List[E]] => List[E] = {
    case StreamF(e, a) => e :: a
  }
  cata[StreamF[E, ?], List[E]](al)
}