/* lambda is the left unitor and rho is the right unitor */
/* <.> is used as compose below */

lambda
<.> bimap(destroy, id)
<.> split == id(rho)
<.> bimap(id, destroy)
<.> split == id;
