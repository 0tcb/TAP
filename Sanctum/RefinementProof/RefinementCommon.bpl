function {:inline} tap_sanctum_perm_eq(tp : addr_perm_t, sp : pte_acl_t) : bool
{ 
  tap_addr_perm_r(tp) == acl2read(sp)  &&
  tap_addr_perm_w(tp) == acl2write(sp) &&
  tap_addr_perm_x(tp) == acl2exec(sp)  &&
  tap_addr_perm_v(tp) == acl2valid(sp)
}

function {:inline} tap_perm_eq(t1 : addr_perm_t, t2 : addr_perm_t) : bool
{ 
  tap_addr_perm_r(t1) == tap_addr_perm_r(t2) &&
  tap_addr_perm_w(t1) == tap_addr_perm_w(t2) &&
  tap_addr_perm_x(t1) == tap_addr_perm_x(t2) &&
  tap_addr_perm_v(t1) == tap_addr_perm_v(t2)
}

function {:inline} disjoint_bitmaps(b1: bv8, b2: bv8) : bool { AND_8(b1, b2) == 0bv8 }

function {:inline} acl2addrperm(acl : pte_acl_t) : addr_perm_t
{ acl[3:2] ++ acl[2:1] ++ acl[4:3] ++ 0bv1 ++ acl[1:0] }

function {:inline} enclave_id_bv2int(input: enclave_id_t): tap_enclave_id_t;
// special enclave id for metadata region.
const tap_metadata_enc_id : tap_enclave_id_t;
const tap_free_enc_id : tap_enclave_id_t;
axiom tap_metadata_enc_id == tap_user_def_enc_id_1;

axiom (forall v1, v2 : enclave_id_t :: 
        v1 != v2 ==> enclave_id_bv2int(v1) != enclave_id_bv2int(v2));
axiom (forall v1 : enclave_id_t :: assigned(v1) ==> valid_enclave_id(enclave_id_bv2int(v1)));
axiom (forall v1 : enclave_id_t :: v1 == null_enclave_id ==> enclave_id_bv2int(v1) == tap_null_enc_id);
axiom (forall v1 : enclave_id_t :: v1 == blocked_enclave_id ==> enclave_id_bv2int(v1) == tap_blocked_enc_id);
axiom (forall v1 : enclave_id_t :: v1 == metadata_enclave_id ==> enclave_id_bv2int(v1) == tap_metadata_enc_id);

axiom (forall v1 : enclave_id_t :: enclave_id_bv2int(v1) != tap_user_def_enc_id_2);
axiom (forall v1 : enclave_id_t :: enclave_id_bv2int(v1) != tap_user_def_enc_id_3);
axiom (forall v1 : enclave_id_t :: enclave_id_bv2int(v1) != tap_user_def_enc_id_4);
axiom (forall v1 : enclave_id_t :: enclave_id_bv2int(v1) != tap_user_def_enc_id_5);
