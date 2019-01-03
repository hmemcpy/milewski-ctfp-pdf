sealed trait Tree[+A]
case class Leaf[A](a: A) extends Tree[A]
case class Node[A](l: Tree[A], r: Tree[A]) extends Tree[A]
// implicit def treeFunctor = ???