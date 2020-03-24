module type Polymorphic_Function_F = {
  type a;
  type b;
  
  let f: a => b;
};
