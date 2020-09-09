module type Ran = {
  type k('a);
  type d('a);
  type ran('a) =
    | Ran({r: 'i. ('a => k('i)) => d('i)});
};
