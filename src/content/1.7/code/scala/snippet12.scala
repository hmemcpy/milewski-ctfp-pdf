implicit val pointEq = new Eq[Point] {
  def ===(a1: Point, a2: Point): Boolean =
    a1.x == a2.x && a1.y == a2.y
}