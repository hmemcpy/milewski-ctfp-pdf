module StringMonoid : Monoid with type t = string = struct
  type t = string

  let mempty = ""
  let mappend = ( ^ )
end
