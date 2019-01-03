def fmap[A, B]: (A => B) => List[A] => List[B] =
  f => {
    case Nil => Nil
    case x :: xs => f(x) :: fmap[A, B](f)(xs)
  }

def sum: List[Double] => Double = _.sum

import math._

def vlen: List[Double] => Double =
  sqrt _ compose sum compose fmap(pow(_, 2))