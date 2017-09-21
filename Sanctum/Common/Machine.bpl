/* Machine specific definitions */

/* The four RISCV modes. */
const RISCV_MODE_U: riscv_mode_t;
const RISCV_MODE_S: riscv_mode_t;
const RISCV_MODE_H: riscv_mode_t;
const RISCV_MODE_M: riscv_mode_t;

axiom RISCV_MODE_U == 0bv2;
axiom RISCV_MODE_S == 1bv2;
axiom RISCV_MODE_H == 2bv2;
axiom RISCV_MODE_M == 3bv2;



//
// Maximum number of pages in the system available for the PT
//
const num_dram_pages: ppn_t;
axiom num_dram_pages == 64bv12;
//
// Max value for vpn1_t.
//
const max_vpn1_t: vpn1_t;
axiom max_vpn1_t == 1023bv10;
//
// Max value for vpn0_t.
//
const max_vpn0_t: vpn0_t;
axiom max_vpn0_t == 1023bv10;

// ----------------------------------------------------------------- //
// Utility functions to manipulate VPNs and PTEs.
// ----------------------------------------------------------------- //
//
// Compute PTE address from PTBR and vpn[1].
//
function {:inline} vpn1ex_to_vpn1(vpn: vpn1ex_t) : vpn1_t
{ vpn[10:0] }
//
// Compute PTE address from PTBR and vpn[1].
//
function {:inline} vpn1_to_pteaddr(base: ppn_t, vpn: vpn1_t) : paddr_t
{ base ++ vpn ++ 0bv2 }
//
// Compute PTE address from PTBR and vpn[0].
//
function {:inline} vpn0_to_pteaddr(base: ppn_t, vpn: vpn0_t) : paddr_t
{ base ++ vpn ++ 0bv2 }
//
// Load the first-level page table entry corresponding to this virtual address.
//
function load_pte1(mem: mem_t, base: ppn_t, vpn1: vpn1_t): word_t
{ LOAD_LE_32(mem, vpn1_to_pteaddr(base, vpn1)) }
//
// Load the second-level page table entry corresponding to this virtual address.
//
function load_pte0(mem: mem_t, base: ppn_t, vpn0: vpn0_t): word_t
{ LOAD_LE_32(mem, vpn0_to_pteaddr(base, vpn0)) }
//
// Convert PPN and ACL into a pte.
function {:inline} pte_from_ppn_acl(ppn: ppn_t, acl: pte_acl_t): word_t
{
  0bv10 ++ ppn ++ acl
}
//
// Get the physical page number from this PTE.
//
function {:inline} pte2ppn(pte: word_t) : ppn_t
{ pte[22:10] }
//
// Get the valid bit of this PTE.
//
function {:inline} pte2valid(pte: word_t) : bv1
{ pte[1:0] }
//
// Get access permission bits
//
function {:inline} pte2rwx(pte: word_t) : bv3
{ pte[4:1] }
//
// Get user bit.
//
function {:inline} pte2user(pte: word_t) : bv1
{ pte[5:4] }
//
// Get all non-ppn bits.
//
function {:inline} pte2acl(pte: word_t): pte_acl_t
{ pte[10:0] }
//
// Extract the valid bit from the ACL.
//
function {:inline} acl2valid(acl: pte_acl_t): bool
{ bv2bool(acl[1:0]) }

function {:inline} acl2read(acl: pte_acl_t): bool
{ bv2bool(acl[2:1]) }

function {:inline} acl2write(acl: pte_acl_t): bool
{ bv2bool(acl[3:2]) }

function {:inline} acl2exec(acl: pte_acl_t): bool
{ bv2bool(acl[4:3]) }

function {:inline} acl2user(acl: pte_acl_t): bool
{ bv2bool(acl[5:4]) }

function {:inline} acl2global(acl: pte_acl_t): bool
{ bv2bool(acl[6:5]) }

function {:inline} acl2accessed(acl: pte_acl_t): bool
{ bv2bool(acl[7:6]) }

function {:inline} acl2dirty(acl: pte_acl_t): bool
{ bv2bool(acl[8:7]) }


// ----------------------------------------------------------------- //
// Extract virtual page numbers from virtual addresses.
function {:inline} vaddr2vpn(vaddr: vaddr_t) : vpn_t
{ vaddr[32:12] }
function {:inline} vaddr2vpn1(vaddr: vaddr_t) : vpn1_t
{ vaddr[32:22] }
function {:inline} vaddr2vpn0(vaddr: vaddr_t) : vpn0_t
{ vaddr[22:12] }
function {:inline} vaddr2offset(vaddr: vaddr_t) : voffset_t
{ vaddr[12:0] }

// ----------------------------------------------------------------- //
// Extract physical page number from physical addresses.
function {:inline} paddr2ppn(paddr: paddr_t) : ppn_t
{ paddr[24:12] }
function {:inline} paddr2offset(paddr: paddr_t) : poffset_t
{ paddr[12:0] }
function {:inline} wpaddr2offset(paddr: wap_addr_t) : wpoffset_t
{ paddr[10:0] }
function {:inline} wpaddr2ppn(paddr: wap_addr_t) : ppn_t
{ paddr[22:10] }
function {:inline} wpaddr2paddr(wpaddr: wap_addr_t): paddr_t
{ wpaddr ++ 0bv2 }
function {:inline} paddr2wpaddr(paddr: paddr_t): wap_addr_t
{ paddr[24:2] }
// Convert a physical page number into a physical address.
function {:inline} ppn2paddr(ppn : ppn_t) : paddr_t
{ ppn ++ 0bv12 }

/* Memory Model */
//function {:inline} STORE_LE_8(mem : mem_t, addr : paddr_t, value : bv8) : mem_t
//function {:inline} STORE_LE_16(mem : mem_t, addr : paddr_t, value : bv16) : mem_t
procedure {:inline 1} STORE_LE_32(mem: mem_t, addr: paddr_t, value: bv32)
   returns (memp: mem_t)
   ensures (LOAD_LE_32(memp, addr) == value);
   ensures (forall a : paddr_t ::
                a[24:2] != addr[24:2] ==> memp[a[24:2]] == mem[a[24:2]]);
{ memp := mem[addr[24:2] := value]; }

procedure {:inline 1} STORE_WORD(mem: mem_t, addr: wap_addr_t, value: word_t)
   returns (memp: mem_t)
   ensures (LOAD_WORD(memp, addr) == value);
   ensures (forall a : wap_addr_t ::
                a != addr ==> memp[a] == mem[a]);
{ memp := mem[addr := value]; }

//function {:inline} STORE_LE_64(mem: mem_t, addr: paddr_t, value: bv64) : mem_t
//  { STORE_LE_32(STORE_LE_32(mem, addr, value[32:0]), PLUS_64(addr, 4bv64), value[64:32]) }

//function {:inline} LOAD_LE_8(mem: mem_t, addr: paddr_t) : bv8
//  { mem[addr] }
//function {:inline} LOAD_LE_16(mem: mem_t, addr: paddr_t) : bv16
//  { LOAD_LE_8(mem, PLUS_64(addr, 1bv64)) ++ LOAD_LE_8(mem, addr) }
function {:inline} LOAD_LE_32(mem: mem_t, addr: paddr_t) : bv32
{ mem[addr[24:2]] }
function {:inline} LOAD_WORD(mem: mem_t, addr: wap_addr_t) : word_t
{ mem[addr] }
//function {:inline} LOAD_LE_64(mem: mem_t, addr: paddr_t) : bv64
//  { LOAD_LE_32(mem, PLUS_64(addr, 4bv64)) ++ LOAD_LE_32(mem, addr) }

function {:inline} dram_region_for(pa: paddr_t) : region_t
  { pa[15:12] } //extract bits 14 - 12, even with rotation. Rotation happens on paddr
function {:inline} dram_region_for_w(pa: wap_addr_t) : region_t
  { pa[13:10] } //extract bits 14 - 12, even with rotation. Rotation happens on paddr
function cache_index_to_int(index : bv9) : int;
function {:inline} sanctum_paddr2set_w(pa : wap_addr_t) : cache_set_index_t
  { cache_index_to_int(dram_region_for_w(pa) ++ pa[19:13]) }
function {:inline} is_word_aligned(pa: paddr_t) : bool
  { pa[2:0] == 0bv2 }

/**********************************
 * Sanctum Helper Functions       *
 **********************************/

function {:inline} is_valid_range_mask_va(mask: vaddr_t) : bool
  { AND_va(mask, PLUS_va(mask, 1bv32)) == 0bv32 }
function {:inline} is_aligned_to_mask_va(addr: vaddr_t, mask: vaddr_t): bool
  { AND_32(addr, mask) == 0bv32 }
function {:inline} is_valid_range_va(base: vaddr_t, mask: vaddr_t) : bool
  { is_aligned_to_mask_va(base, mask) && is_valid_range_mask_va(mask) }
function {:inline} is_in_evrange(evbase : vaddr_t, evmask : vaddr_t, addr : vaddr_t) : bool
  { AND_va(addr, evmask) == evbase }
function {:inline} is_valid_range_mask_pa(mask: paddr_t) : bool
  { AND_pa(mask, PLUS_pa(mask, k1_paddr_t)) == k0_paddr_t }
function {:inline} is_aligned_to_mask_pa(addr: paddr_t, mask: paddr_t): bool
  { AND_pa(addr, mask) == k0_paddr_t }
function {:inline} is_valid_range_pa(base: paddr_t, mask: paddr_t) : bool
  { is_aligned_to_mask_pa(base, mask) && is_valid_range_mask_pa(mask) }
function {:inline} is_dram_address(addr: paddr_t) : bool
  { LT_pa(addr, 262144bv24) } //256 KB so 1 << 18
function {:inline} is_valid_dram_region(r: region_t) : bool
  { LE_r(r, 7bv3) } //8 regions possible
function {:inline} is_dynamic_dram_region(r: region_t) : bool
  { r != 0bv3 && is_valid_dram_region(r) } //can the region be freed and reassigned?
function {:inline} is_valid_enclave_id(enclave_metadata_valid: eid2bool_map_t, e: enclave_id_t) : bool
  { enclave_metadata_valid[e] }
function {:inline} clamped_dram_region_for(addr: paddr_t) : region_t
  { if(is_dram_address(addr)) then dram_region_for(addr) else 0bv3 }
function {:inline} is_page_aligned_pa(addr: paddr_t) : bool
  { is_aligned_to_mask_pa(addr, 4095bv24) }
function {:inline} is_page_aligned_va(addr: vaddr_t) : bool
  { is_aligned_to_mask_va(addr, 4095bv32) }

function {:inline} read_bitmap(bmap: bitmap_t, r: region_t): bv1
{ RSHIFT_8(bmap, 0bv5 ++ r)[1:0] }

function {:inline} bitmap_set_bit(bmap: bitmap_t, index: region_t): bitmap_t
{ OR_8(bmap, LSHIFT_8(1bv8, 0bv5 ++ index)) }

function {:inline} bitmap_clear_bit(bmap: bitmap_t, index: region_t): bitmap_t
{ AND_8(bmap, NOT_8(LSHIFT_8(1bv8, 0bv5 ++ index))) }

// ASSUME paddr_t --> bv32
function {:inline} region_to_eid(region: region_t) : enclave_id_t
{ 0bv9 ++ region ++ 0bv12 }

function {:inline} region_to_eid_arb(region: region_t) : enclave_id_t
{ 0bv9 ++ region ++ 0bv12 }

function {:inline} region_to_tid(region: region_t) : enclave_id_t
{ 1bv9 ++ region ++ 0bv12 }
// ENDASSUME paddr_t --> bv32

function {:inline} wpoffset1ex_to_wpoffset(w: wpoffset1ex_t) : wpoffset_t
{ w[10:0] }
