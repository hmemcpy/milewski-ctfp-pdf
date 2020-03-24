module Test_Functor_Id = (F: Functor) => {
  open F;
  
  let test_id = x => assert(fmap(id, x) == x);
};
