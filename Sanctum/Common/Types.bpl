/* Types */
type riscv_mode_t = bv2;
type riscv_access_t;
const unique riscv_access_read: riscv_access_t;
const unique riscv_access_write: riscv_access_t;
const unique riscv_access_fetch: riscv_access_t;
function {:inline} valid_access(a : riscv_access_t) : bool {
  a == riscv_access_read    || a == riscv_access_write   || a == riscv_access_fetch
}

axiom (forall ra: riscv_access_t :: (ra == riscv_access_read    ||
                                     ra == riscv_access_write   ||
                                     ra == riscv_access_fetch));

type paddr_t = bv24;
type wap1ex_addr_t = bv23; // word aligned physical addr + 1 extra bit.
type region_t = bv3;
type bitmap_t = bv8;
type api_result_t = bv3;
type enclave_id_t = paddr_t;
type thread_id_t = paddr_t;
type vpn_t = bv20;
type vpn1_t = bv10;
type vpn1ex_t = bv11;
type vpn0_t = bv10;
type voffset_t = bv12;
type wpoffset_t = bv10;
type wpoffset1ex_t = bv11;
type poffset_t = bv12;
type ppn_t = bv12;
type pte_acl_t = bv10;
type used_page_map_t = [ppn_t]bool;
type ptbl_acl_map_t = [ppn_t, vpn_t] pte_acl_t;
type ptbl_addr_map_t = [ppn_t, vpn_t] ppn_t;
type eid2bool_map_t = [enclave_id_t] bool;
/* constant enclave_id_t values. */
const null_enclave_id : enclave_id_t;
axiom null_enclave_id == 0bv24;
const blocked_enclave_id : enclave_id_t;
axiom blocked_enclave_id == 1bv24;
const metadata_enclave_id : enclave_id_t;
axiom metadata_enclave_id == 2bv24;
const free_enclave_id : enclave_id_t;
axiom free_enclave_id == 3bv24;
/* constant paddr_t values. */
const k0_paddr_t : paddr_t;
axiom k0_paddr_t == 0bv24;
const k1_paddr_t : paddr_t;
axiom k1_paddr_t == 1bv24;
/* constant vaddr_t values. */
const kPGSZ_vaddr_t : vaddr_t;
axiom kPGSZ_vaddr_t == 4096bv32;
/* const wap_addr_t values. */
const kPGSZ_wap_addr_t : wap_addr_t;
axiom kPGSZ_wap_addr_t == 4096bv22;
/* constant ppn_t values. */
const k0_ppn_t : ppn_t;
axiom k0_ppn_t == 0bv12;
const k1_ppn_t : ppn_t;
axiom k1_ppn_t == 1bv12;
const k2_ppn_t : ppn_t;
axiom k2_ppn_t == 2bv12;
/* constant vpn_t values. */
const k0_vpn_t : vpn_t;
axiom k0_vpn_t == 0bv20;
const k1_vpn_t : vpn_t;
axiom k1_vpn_t == 1bv20;
const kmax_vpn_t : vpn_t;
axiom kmax_vpn_t == 1048575bv20;
/* constant vpn1ex_t values. */
const k0_vpn1ex : vpn1ex_t;
axiom k0_vpn1ex == 0bv11;
const k1_vpn1ex : vpn1ex_t;
axiom k1_vpn1ex == 1bv11;
/* constant pte_acl_t values. */
const k_pg_invalid_acl : pte_acl_t;
axiom k_pg_invalid_acl == 0bv10;
const k_pg_valid_acl : pte_acl_t;
axiom k_pg_valid_acl == 1bv10;
/* constant bitmap_t values. */
const k0_bitmap_t : bitmap_t;
axiom k0_bitmap_t == 0bv8;
const k1_bitmap_t : bitmap_t;
axiom k1_bitmap_t == 1bv8;
/* constant region_t values. */
const k0_region_t : region_t;
axiom k0_region_t == 0bv3;
const k1_region_t : region_t;
axiom k1_region_t == 1bv3;
const k2_region_t : region_t;
axiom k2_region_t == 2bv3;
const k3_region_t : region_t;
axiom k3_region_t == 3bv3;
const k4_region_t : region_t;
axiom k4_region_t == 4bv3;
const k5_region_t : region_t;
axiom k5_region_t == 5bv3;
const k6_region_t : region_t;
axiom k6_region_t == 6bv3;
const k7_region_t : region_t;
axiom k7_region_t == 7bv3;
const kN_region_t : region_t;
axiom kN_region_t == 7bv3;

const kEV_BASE_vaddr_t : vaddr_t;
axiom kEV_BASE_vaddr_t == 4294901760bv32;
const kEV_MASK_vaddr_t : vaddr_t;
axiom kEV_MASK_vaddr_t == 65535bv32;

const k0_wpoffset_t : wpoffset_t;
axiom k0_wpoffset_t == 0bv10;
const k1_wpoffset_t : wpoffset_t;
axiom k1_wpoffset_t == 1bv10;
const kN_wpoffset_t : wpoffset_t;
axiom kN_wpoffset_t == 1023bv10;

const k0_wpoffset1ex_t : wpoffset1ex_t;
axiom k0_wpoffset1ex_t  == 0bv11;
const k1_wpoffset1ex_t : wpoffset1ex_t;
axiom k1_wpoffset1ex_t  == 1bv11;
const k1024_wpoffset1ex_t : wpoffset1ex_t;
axiom k1024_wpoffset1ex_t  == 1024bv11;

const kmax_pte_acl_t_as_int : int;
axiom kmax_pte_acl_t_as_int == 1023; // max(bv10)

function pte_acl2int(va : pte_acl_t) : int;
axiom (forall v1, v2 : pte_acl_t :: (v1 != v2) ==> (pte_acl2int(v1) != pte_acl2int(v2)));
axiom (forall w : pte_acl_t :: pte_acl2int(w) >= 0 && pte_acl2int(w) <= kmax_pte_acl_t_as_int);
