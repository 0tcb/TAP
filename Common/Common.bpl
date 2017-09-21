/** Common functions. 
  * 
  * Functions used in both the TAP and Sanctum/SGX.
  *
  */

//--------------------------------------------------------------------------//
// Hash.                                                                    //
//--------------------------------------------------------------------------//
function update_digest(x : int, m : measurement_t) : measurement_t;

//--------------------------------------------------------------------------//
// collision resistant                                                      //
//--------------------------------------------------------------------------//
axiom (forall x1, x2 : int, t1, t2 : measurement_t :: 
            ((x1 != x2) || (t1 != t2)) <==> (update_digest(x1, t1) != update_digest(x2, t2)));

//--------------------------------------------------------------------------//
// second-preimage resistant                                                //
//--------------------------------------------------------------------------//
axiom (forall x1, x2 : int, t1, t2 : measurement_t ::
            (update_digest(x1, t1) == update_digest(x2, t2)) <==> (x1 == x2 && t1 == t2));

