module ProfunctorArrow : Profunctor = struct
  type ('a, 'b) p = 'a -> 'b

  let dimap f g p = compose g (compose p f)
end

module ProfunctorExtArrow : ProfunctorExt = struct
  type ('a, 'b) p = 'a -> 'b

  let lmap f p = (flip compose) f p
  let rmap = compose
end
