module type Terminal_IO = {
  /* ReasonML doesn't have a built-in IO type*/
  type io('a) =
    | IO(unit => 'a);

  let get_char: unit => io(char);
};
