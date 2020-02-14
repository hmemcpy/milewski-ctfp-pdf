module type Terminal_IO = sig
  (* OCaml doesn't have a built-in IO type*)
  type 'a io = IO of (unit -> 'a)

  val get_char : unit -> char io
end
