module type Exp = {
  type a;
  type b;
  type d('a) =
    | I('a);
  type k('a) = ('a, a);

  include
    Lan with type k('a) := (a, 'a) 
      and type d('a) := d('a) 
      and type a := b;
};
