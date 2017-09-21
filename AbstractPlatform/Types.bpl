// -------------------------------------------------------------------- //
// registers.                                                           //
// -------------------------------------------------------------------- //
type regindex_t = int;
type regs_t = [regindex_t] word_t;
function LE_ri(p1: regindex_t, p2: regindex_t) : bool { p1 <= p2 }
function LT_ri(p1: regindex_t, p2: regindex_t) : bool { p1 < p2 }
function PLUS_ri(p1: regindex_t, p2: regindex_t) : regindex_t { p1 + p2 }
function MINUS_ri(p1: regindex_t, p2: regindex_t) : regindex_t { p1 - p2 }
const k0_regindex_t : int;
axiom k0_regindex_t == 0;
const k1_regindex_t : int;
axiom k1_regindex_t == 1;
const kmax_regindex_t : int;
axiom kmax_regindex_t == 511;
const kN_regindex_t : int;
axiom kN_regindex_t == 512;

const kN_regindex_t_as_int : int;
axiom kN_regindex_t_as_int == 512;
function valid_regindex(ri : regindex_t) : bool 
{ ri >= k0_regindex_t && ri < kN_regindex_t }


// -------------------------------------------------------------------- //
// operating mode of the CPU.                                           //
// -------------------------------------------------------------------- //
type mode_t;
const unique mode_untrusted : mode_t;
const unique mode_enclave   : mode_t;
axiom (forall m : mode_t :: m == mode_untrusted || m == mode_enclave);

// -------------------------------------------------------------------- //
// Page Tables (sort of: because we map addresses and not pages).       //
// -------------------------------------------------------------------- //
type addr_perm_t    = bv5; // see kmax_addr_perm_t_as_int below.
type vaddr2bool_t   = [vaddr_t]bool;
type excl_vaddr_t   = [vaddr_t]bool;
type addr_valid_t   = [vaddr_t]addr_perm_t;
type addr_map_t     = [vaddr_t]wap_addr_t;

const k0_addr_perm_t : addr_perm_t;
const kmax_addr_perm_t_as_int : int; 
axiom k0_addr_perm_t == 0bv5;
axiom kmax_addr_perm_t_as_int == 31;

// getters.
function tap_addr_perm_p(p : addr_perm_t) : bool { p[1:0] == 1bv1 }   // Present
function tap_addr_perm_a(p : addr_perm_t) : bool { p[2:1] == 1bv1 }   // Accessed
function tap_addr_perm_x(p : addr_perm_t) : bool { p[3:2] == 1bv1 }   // eXecute (fetch)
function tap_addr_perm_r(p : addr_perm_t) : bool { p[4:3] == 1bv1 }   // Read (load)
function tap_addr_perm_w(p : addr_perm_t) : bool { p[5:4] == 1bv1 }   // Write (store)

// valid is equivalent to being either fetchable/readable/writeable.
function tap_addr_perm_v(p : addr_perm_t) : bool
{ tap_addr_perm_x(p) || tap_addr_perm_r(p) || tap_addr_perm_w(p) }

// setters.
function tap_set_addr_perm_p(p : addr_perm_t) : addr_perm_t { p[5:1] ++ 1bv1           }
function tap_set_addr_perm_a(p : addr_perm_t) : addr_perm_t { p[5:2] ++ 1bv1 ++ p[1:0] }
function tap_set_addr_perm_x(p : addr_perm_t) : addr_perm_t { p[5:3] ++ 1bv1 ++ p[2:0] }
function tap_set_addr_perm_r(p : addr_perm_t) : addr_perm_t { p[5:4] ++ 1bv1 ++ p[3:0] }
function tap_set_addr_perm_w(p : addr_perm_t) : addr_perm_t {           1bv1 ++ p[4:0] }

// remove the "irrelevant" (OS-settable) bits from addr_perm_t
function tap_addr_perm_bits(p : addr_perm_t) : addr_perm_t
{ p[5:2] ++ 0bv2 }

// predicates
function tap_addr_perm_eq(p1 : addr_perm_t, p2 : addr_perm_t) : bool
{ 
    tap_addr_perm_x(p1) == tap_addr_perm_x(p2) &&
    tap_addr_perm_r(p1) == tap_addr_perm_r(p2) &&
    tap_addr_perm_w(p1) == tap_addr_perm_w(p2) 
}

// -------------------------------------------------------------------- //
// enclave types.                                                       //
// -------------------------------------------------------------------- //
type tap_enclave_id_t                   = int;
type tap_thread_id_t                    = int;
type count_t                            = int;
const k0_tap_thread_id_t : tap_thread_id_t;
axiom k0_tap_thread_id_t == 0;

type container_data_t                       = [wap_addr_t]word_t;
type container_valid_t                      = [wap_addr_t]bool;
// what enclaves exist in the system? 
type tap_enclave_metadata_valid_t           = [tap_enclave_id_t]bool;
// what is the state of the enclave?
type tap_enclave_metadata_regs_t            = [tap_enclave_id_t]regs_t;
type tap_enclave_metadata_num_threads_t     = [tap_enclave_id_t]count_t;
type tap_enclave_metadata_entrypoint_t      = [tap_enclave_id_t]vaddr_t;
type tap_enclave_metadata_pc_t              = [tap_enclave_id_t]vaddr_t;
// what memory is an enclave allowed to access?
type tap_enclave_metadata_addr_valid_t      = [tap_enclave_id_t]addr_valid_t;
type tap_enclave_metadata_addr_excl_t       = [tap_enclave_id_t]excl_vaddr_t;
type tap_enclave_metadata_addr_map_t        = [tap_enclave_id_t]addr_map_t;
// what addresses are exclusive to an enclave.
type excl_map_t                             = [wap_addr_t]bool;
type shared_paddr_map_t                     = [wap_addr_t]bool;
type shared_vaddr_map_t                     = [vaddr_t]bool;
type paddr2paddr_map_t                      = [wap_addr_t]wap_addr_t;
type owner_map_t                            = [wap_addr_t]tap_enclave_id_t;
// what is the measurement of this enclave?
type tap_enclave_metadata_measurement_t     = [tap_enclave_id_t]measurement_t;
// has this enclave been paused?
type tap_enclave_metadata_paused_t          = [tap_enclave_id_t]bool;
// do the cache sets of this enclave conflict with rest of memory?
type tap_enclave_metadata_cache_conflict_t  = [tap_enclave_id_t]bool;

// enclave API call results.
type enclave_op_result_t;
const unique enclave_op_success     : enclave_op_result_t;
const unique enclave_op_invalid_arg : enclave_op_result_t;
const unique enclave_op_failed      : enclave_op_result_t;
axiom (forall m : enclave_op_result_t :: m == enclave_op_success         ||
                                         m == enclave_op_invalid_arg     ||
                                         m == enclave_op_failed);

type tap_proof_op_t;
const unique tap_proof_op_launch     : tap_proof_op_t;
const unique tap_proof_op_enter      : tap_proof_op_t;
const unique tap_proof_op_exit       : tap_proof_op_t;
const unique tap_proof_op_resume     : tap_proof_op_t;
const unique tap_proof_op_pause      : tap_proof_op_t;
const unique tap_proof_op_compute    : tap_proof_op_t;
const unique tap_proof_op_destroy    : tap_proof_op_t;
const unique tap_proof_op_release    : tap_proof_op_t;
const unique tap_proof_op_block      : tap_proof_op_t;

axiom (forall o : tap_proof_op_t :: 
        o == tap_proof_op_compute   ||
        o == tap_proof_op_destroy   ||
        o == tap_proof_op_enter     ||
        o == tap_proof_op_exit      ||
        o == tap_proof_op_launch    ||
        o == tap_proof_op_resume    ||
        o == tap_proof_op_pause     ||
        o == tap_proof_op_release   ||
        o == tap_proof_op_block);
function tap_proof_op_valid(o : tap_proof_op_t) : bool 
{
    o == tap_proof_op_compute   || o == tap_proof_op_destroy   ||
    o == tap_proof_op_enter     || o == tap_proof_op_exit      ||
    o == tap_proof_op_launch    || o == tap_proof_op_resume    ||
    o == tap_proof_op_pause     || o == tap_proof_op_release   ||
    o == tap_proof_op_block
}

function tap_proof_op_valid_in_enclave(o : tap_proof_op_t) : bool
{
    o == tap_proof_op_compute   ||
    o == tap_proof_op_exit      ||
    o == tap_proof_op_pause
}

// -------------------------------------------------------------------- //
// constants for enclaves.                                              //
// -------------------------------------------------------------------- //
const tap_null_enc_id : tap_enclave_id_t;
axiom tap_null_enc_id == 0;
const tap_blocked_enc_id : tap_enclave_id_t;
axiom tap_blocked_enc_id == 1;
const tap_user_def_enc_id_1 : tap_enclave_id_t;
axiom tap_user_def_enc_id_1 == 2;
const tap_user_def_enc_id_2 : tap_enclave_id_t;
axiom tap_user_def_enc_id_2 == 3;
const tap_user_def_enc_id_3 : tap_enclave_id_t;
axiom tap_user_def_enc_id_3 == 4;
const tap_user_def_enc_id_4 : tap_enclave_id_t;
axiom tap_user_def_enc_id_4 == 5;
const tap_user_def_enc_id_5 : tap_enclave_id_t;
axiom tap_user_def_enc_id_5 == 6;

function valid_enclave_id(id : tap_enclave_id_t) : bool
{ 
  id != tap_null_enc_id       && id != tap_blocked_enc_id    &&
  id != tap_user_def_enc_id_1 && id != tap_user_def_enc_id_2 &&
  id != tap_user_def_enc_id_3 && id != tap_user_def_enc_id_4 &&
  id != tap_user_def_enc_id_5
}

function special_enclave_id(id : tap_enclave_id_t) : bool
{
  id == tap_blocked_enc_id    || id == tap_user_def_enc_id_1 ||
  id == tap_user_def_enc_id_2 || id == tap_user_def_enc_id_3 ||
  id == tap_user_def_enc_id_4 || id == tap_user_def_enc_id_5
}

// -------------------------------------------------------------------- //

// -------------------------------------------------------------------- //
// exceptions                                                           //
// -------------------------------------------------------------------- //
type exception_t;
const unique excp_none                      : exception_t; // all iz well
const unique excp_os_protection_fault       : exception_t; // os prot violation
const unique excp_tp_protection_fault       : exception_t; // trusted platform
axiom (forall e : exception_t :: e == excp_none                 ||
                                 e == excp_os_protection_fault  ||
                                 e == excp_tp_protection_fault);

