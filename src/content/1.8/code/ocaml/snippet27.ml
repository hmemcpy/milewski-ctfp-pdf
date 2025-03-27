(* Available as Fun.flip in the standard library *)
let flip (f : 'a -> 'b -> 'c) (x : 'b) (y : 'a) : 'c = f y x
