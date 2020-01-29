module StringMonoid : Monoid = struct
  type a = string

  let mempty = ""
  let mappend = ( ^ )
end
