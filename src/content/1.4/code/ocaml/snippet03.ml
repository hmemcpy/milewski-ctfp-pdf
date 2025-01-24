module type Fish_sig = sig
  val ( >=> ) : ('a -> 'b writer) ->
                ('b -> 'c writer) -> 'a -> 'c writer
end
