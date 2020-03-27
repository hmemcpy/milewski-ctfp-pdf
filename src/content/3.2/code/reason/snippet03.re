module type Counit_Example = {
  type w('c);

  let extract: w('c) => 'c;
};
