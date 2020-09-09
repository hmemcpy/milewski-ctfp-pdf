module KleisliIdentity = {
  let return: 'a => writer('a) = a => (a, "");
};
