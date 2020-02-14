module type Lan = sig
  type 'a k
  type 'a d
  type a
  type i

  val fk : i k -> a
  val di : i d
end
