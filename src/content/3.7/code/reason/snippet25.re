module type Comonoid = {
  type m;

  let split: m => (m, m);
  let destroy: m => unit;
};
