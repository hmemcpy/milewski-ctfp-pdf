let pred_to_str =
  fun
  | Op(f) => Op(x => (f(x)) ? "T" : "F");
