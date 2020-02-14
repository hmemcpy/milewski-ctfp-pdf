module type T = sig
  type t
end

module Partially_Applied_FunctionType (T : T) = struct
  type 'b t = T.t -> 'b
end
