module type Reader_Fmap_Example = {
  let fmap: ('a => 'b, 'r => 'a, 'r) => 'b;
};
