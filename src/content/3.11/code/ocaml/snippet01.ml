module type Ran = sig
  type 'a k
  type 'a d
  type 'a ran = Ran of { r : 'i. ('a -> 'i k) -> 'i d }
end
