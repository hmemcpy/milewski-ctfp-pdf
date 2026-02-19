module Coend (P : Profunctor) = struct
  type coend = Coend of { c : 'a. ('a, 'a) P.t }
end
