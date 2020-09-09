module type Kleisli = {
  type a;
  type b;
  type c;
  
  let (>=>): (a => writer(b), b => writer(c), a) => writer(c);
};
