module type Kleisli = sig
  type a
  type b
  type c

  val ( >=> ) : (a -> b writer) -> (b -> c writer) -> a -> c writer
end
