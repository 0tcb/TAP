//TODO: State aliasing assumptions

/**********************************
 * Ghost State                    *
 **********************************/

var owner                               : [region_t] enclave_id_t;
var blocked_at                          : [region_t] int;

var enclave_metadata_valid              : eid2bool_map_t;
var enclave_metadata_is_initialized     : eid2bool_map_t;
var enclave_metadata_ev_base            : [enclave_id_t] vaddr_t;
var enclave_metadata_ev_mask            : [enclave_id_t] vaddr_t;
var enclave_metadata_bitmap             : [enclave_id_t] bitmap_t;
var enclave_metadata_load_eptbr         : [enclave_id_t] ppn_t;
var enclave_metadata_dram_region_count  : [enclave_id_t] word_t;
var enclave_metadata_last_load_addr     : [enclave_id_t] paddr_t;
var enclave_metadata_thread_count       : [enclave_id_t] int;

var thread_metadata_valid               : [thread_id_t] bool;
var thread_metadata_eid                 : [thread_id_t] enclave_id_t;
var thread_metadata_entry_pc            : [thread_id_t] vaddr_t;
var thread_metadata_entry_stack         : [thread_id_t] vaddr_t;
var thread_metadata_fault_pc            : [thread_id_t] vaddr_t;
var thread_metadata_fault_stack         : [thread_id_t] vaddr_t;

var os_bitmap                           : bitmap_t;

var os_pc                               : vaddr_t;
var dram_regions_info_block_clock       : int;

/**********************************
 * Constants                      *
 **********************************/

const enclave_metadata_valid_init: eid2bool_map_t;
axiom (forall i: enclave_id_t :: enclave_metadata_valid_init[i] == false);
const thread_metadata_valid_init: [thread_id_t] bool;
axiom (forall i: thread_id_t :: thread_metadata_valid_init[i] == false);

const monitor_ok: api_result_t;
axiom monitor_ok == 0bv3;
const monitor_invalid_value: api_result_t;
axiom monitor_invalid_value == 1bv3;
const monitor_invalid_state: api_result_t;
axiom monitor_invalid_state == 2bv3;
const monitor_unknown_error: api_result_t;
axiom monitor_unknown_error == 3bv3;
const monitor_access_denied: api_result_t;
axiom monitor_access_denied == 4bv3;
const monitor_unsupported: api_result_t;
axiom monitor_unsupported == 5bv3;

function {:inline} assigned(r: enclave_id_t) : bool
  { r != null_enclave_id && r != free_enclave_id && r != blocked_enclave_id && r != metadata_enclave_id } //can the region be freed and reassigned?

/**********************************
 * Sanctum Monitor APIs           *
 **********************************/

procedure {:inline 1} initialize_sanctum()
 modifies cpu_evbase,
          cpu_evmask,
          cpu_eptbr,
          cpu_ptbr,
          cpu_drbmap,
          cpu_edrbmap,
          cpu_parbase,
          cpu_eparbase,
          cpu_parmask,
          cpu_eparmask,
          cpu_dmarbase,
          cpu_dmarmask,
          owner,
          core_info_enclave_id,
          core_info_thread_id,
          enclave_metadata_valid,
          thread_metadata_valid,
          os_bitmap;
{
  var ri : region_t;

  cpu_evbase := k0_vaddr_t;
  cpu_evmask := k0_vaddr_t;
  cpu_eptbr := k0_ppn_t;
  cpu_ptbr := k2_ppn_t; //falls in region 0, which is owned by the OS
  cpu_drbmap := k1_bitmap_t; //OS owns regions {0,1}
  cpu_edrbmap := k0_bitmap_t; //no enclaves yet

  cpu_parbase := 0bv9 ++ 0bv3 ++ 0bv12;
  cpu_parmask := 0bv9 ++ 0bv3 ++ 255bv12;
  cpu_eparbase := cpu_parbase;
  cpu_eparmask := cpu_parmask;

  cpu_dmarbase := 0bv9 ++ 0bv3 ++ 256bv12;
  cpu_dmarmask := 0bv9 ++ 0bv3 ++ 255bv12;

  ri := k0_region_t;
  while (LT_r(ri, kN_region_t))
   invariant (forall r : region_t :: LT_r(r, ri) ==> owner[r] == free_enclave_id);
  {
   owner[ri] := free_enclave_id;
   ri := PLUS_r(ri, k1_region_t);
  }
  owner[kN_region_t]    := free_enclave_id;
  assert (forall r : region_t :: owner[r] == free_enclave_id);

  owner[k0_region_t]    := null_enclave_id;
  assert (forall r : region_t :: r != k0_region_t ==> owner[r] == free_enclave_id);
  assert (owner[k0_region_t] == null_enclave_id);
  core_info_enclave_id  := null_enclave_id;

  enclave_metadata_valid := enclave_metadata_valid_init;
  thread_metadata_valid := thread_metadata_valid_init;

  os_bitmap := 1bv8; //OS owns regions {0}
}

procedure {:inline 1} create_metadata_region(region: region_t)
  returns (result: api_result_t)
  modifies owner;
{
  //must be called by OS
  if (core_info_enclave_id != null_enclave_id) {
    result := monitor_invalid_value; return;
  }

  if (!is_valid_dram_region(region)) {
    result := monitor_invalid_value; return;
  }

  //can only convert a free region into a metadata region
  if (owner[region] != free_enclave_id) {
    result := monitor_invalid_state; return;
  }

  owner[region] := metadata_enclave_id;

  result := monitor_ok; return;
}

procedure {:inline 1} create_enclave(eid: enclave_id_t, evbase: vaddr_t, evmask: vaddr_t)
  returns (result: api_result_t)
  modifies enclave_metadata_valid,
           enclave_metadata_is_initialized,
           enclave_metadata_ev_base,
           enclave_metadata_ev_mask,
           enclave_metadata_bitmap,
           enclave_metadata_thread_count,
           enclave_metadata_load_eptbr,
           enclave_metadata_dram_region_count,
           enclave_metadata_last_load_addr;
{
  var dram_region : region_t;

  //must be called by OS
  if (core_info_enclave_id != null_enclave_id) {
    result := monitor_invalid_value; return;
  }

  if (!is_valid_range_va(evbase, evmask)) {
    result := monitor_invalid_value; return;
  }

  //enclave must get at least a page of virtual address space
  if (LT_va(PLUS_va(evmask, k1_vaddr_t), kPGSZ_vaddr_t)) {
    result := monitor_invalid_value; return;
  }

  //metadata must live within DRAM
  if (!is_dram_address(eid) || !is_page_aligned_pa(eid)) {
    result := monitor_invalid_value; return;
  }

  dram_region := dram_region_for(eid);
  if (owner[dram_region] != metadata_enclave_id) {
    result := monitor_invalid_value; return;
  }

  /* BUG: missing check */
  if (enclave_metadata_valid[eid]) {
    result := monitor_invalid_state; return;
  }

  /* BUG: missing check */
  if (!assigned(eid)) {
    result := monitor_invalid_value; return;
  }

  enclave_metadata_valid[eid] := true;
  enclave_metadata_thread_count[eid] := 0;
  enclave_metadata_is_initialized[eid] := false;
  enclave_metadata_ev_base[eid] := evbase;
  enclave_metadata_ev_mask[eid] := evmask;
  enclave_metadata_bitmap[eid] := k0_bitmap_t;
  enclave_metadata_load_eptbr[eid] := k0_ppn_t;
  enclave_metadata_dram_region_count[eid] := k0_word_t;
  enclave_metadata_last_load_addr[eid] := k0_paddr_t;

  result := monitor_ok; return;
}

procedure {:inline 1} load_page_table(eid: enclave_id_t, vaddr: vaddr_t, paddr: paddr_t, acl: pte_acl_t, level: int)
  returns (result: api_result_t)
  modifies enclave_metadata_load_eptbr, cpu_ptbr;
  modifies ptbl_addr_map, ptbl_acl_map;
{
  var pte: word_t;
  var ptbr: ppn_t;
  var eptbr_p: ppn_t;
  var paddr_region: region_t;
  var eid_region: region_t;
  var success: bool;

  //must be called by OS
  if (core_info_enclave_id != null_enclave_id) {
    result := monitor_invalid_value; return;
  }

  if (level < 0 || level > 2) {
    result := monitor_invalid_value;
    return;
  }

  if (!is_dram_address(paddr)) {
    result := monitor_invalid_value; return;
  }

  if (!is_page_aligned_pa(paddr)) {
    result := monitor_invalid_value; return;
  }

  // valid enclave?
  if (eid != null_enclave_id && !is_valid_enclave_id(enclave_metadata_valid, eid)) {
    result := monitor_invalid_value;
    return;
  }

  if (eid == null_enclave_id && level != 2) {
    result := monitor_invalid_value;
    return;
  }

  if (enclave_metadata_is_initialized[eid]) {
    result := monitor_invalid_state;
    return;
  }

  // FIXME: verify this.
  // we don't own this region so can't allow page tables to be outside it.
  paddr_region := dram_region_for(paddr);
  if (owner[paddr_region] != eid && level > 0) {
    result := monitor_invalid_value;
    return;
  }

  if (level == 2) {
    if (eid == null_enclave_id) {
      cpu_ptbr := paddr2ppn(paddr);
    } else {
      enclave_metadata_load_eptbr[eid] := paddr2ppn(paddr);
      assert (forall e: enclave_id_t :: e != eid ==> enclave_metadata_load_eptbr[e] == old(enclave_metadata_load_eptbr[e]));
    }
    result := monitor_ok;
  } else {
    ptbr := if (eid == null_enclave_id) then cpu_ptbr else enclave_metadata_load_eptbr[eid];
    call success := create_page_table_mapping(ptbr, vaddr, paddr, acl);
    result := if (success) then monitor_ok else monitor_unknown_error;
    assert (result == monitor_ok ==> ptbl_acl_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(vaddr)] == acl);
    assert (result == monitor_ok ==> translate_vaddr2paddr(ptbl_addr_map, enclave_metadata_load_eptbr[eid], vaddr) ==
                                     (paddr2ppn(paddr) ++ vaddr2offset(vaddr)));
  }
}

procedure {:inline 1} assign_dram_region(region: region_t, new_owner: enclave_id_t)
  returns (result: api_result_t)
  modifies owner, enclave_metadata_bitmap, os_bitmap, cpu_drbmap;
{
  //must be called by OS
  if (core_info_enclave_id != null_enclave_id) {
    result := monitor_invalid_value; return;
  }

  if (!is_valid_dram_region(region)) {
    result := monitor_invalid_value; return;
  }

  if (!enclave_metadata_valid[new_owner]) {
    result := monitor_invalid_value; return;
  }

  if (enclave_metadata_is_initialized[new_owner]) {
    result := monitor_invalid_state; return;
  }

  //can only assign free dram regions
  if (owner[region] != free_enclave_id) {
    result := monitor_invalid_state; return;
  }

  owner[region] := new_owner;
  if (new_owner == null_enclave_id) {
    os_bitmap := bitmap_set_bit(os_bitmap, region);
    cpu_drbmap := os_bitmap;
  } else {
    enclave_metadata_bitmap[new_owner] := bitmap_set_bit(enclave_metadata_bitmap[new_owner], region);
  }

  result := monitor_ok;
}

procedure {:inline 1} load_thread(eid: enclave_id_t, tid: thread_id_t, entry_pc: vaddr_t, entry_stack: vaddr_t, fault_pc: vaddr_t, fault_stack: vaddr_t)
  returns (result: api_result_t)
  modifies thread_metadata_valid,
           thread_metadata_eid,
           thread_metadata_entry_pc,
           thread_metadata_entry_stack,
           thread_metadata_fault_pc,
           thread_metadata_fault_stack,
           enclave_metadata_thread_count;
{
  //must be called by OS
  if (core_info_enclave_id != null_enclave_id) {
    result := monitor_invalid_value; return;
  }

  if (!is_valid_enclave_id(enclave_metadata_valid, eid)) {
    result := monitor_invalid_value; return;
  }

  if (enclave_metadata_is_initialized[eid]) {
    result := monitor_invalid_state; return;
  }
  //if (enclave_metadata_load_eptbr[eid] == k0_paddr_t) {
  //  result := monitor_invalid_state; return;
  //}

  thread_metadata_valid[tid] := true;
  thread_metadata_eid[tid] := eid;
  thread_metadata_entry_pc[tid] := entry_pc;
  thread_metadata_entry_stack[tid] := entry_stack;
  thread_metadata_fault_pc[tid] := fault_pc;
  thread_metadata_fault_stack[tid] := fault_stack;

  enclave_metadata_thread_count[eid] := enclave_metadata_thread_count[eid] + 1;

  result := monitor_ok;
}

procedure {:inline 1} init_enclave(eid: enclave_id_t)
  returns (result: api_result_t)
  modifies enclave_metadata_is_initialized;
{
  //must be called by OS
  if (core_info_enclave_id != null_enclave_id) {
    result := monitor_invalid_value; return;
  }

  if (!assigned(eid) || !is_valid_enclave_id(enclave_metadata_valid, eid)) {
    result := monitor_invalid_state; return;
  }
  if (enclave_metadata_is_initialized[eid]) {
    result := monitor_invalid_state; return;
  }
  if (owner[dram_region_for(enclave_metadata_load_eptbr[eid] ++ 0bv12)] != eid) {
    result := monitor_invalid_state; return;
  }

  enclave_metadata_is_initialized[eid] := true;
  result := monitor_ok;
}


procedure {:inline 1} enter_enclave(eid: enclave_id_t, tid: thread_id_t)
  returns  (result: api_result_t)
  modifies core_info_enclave_id,
           core_info_thread_id,
           cpu_evbase,
           cpu_evmask,
           cpu_edrbmap,
           cpu_eptbr,
           rip;
{
  //must be called by OS
  if (core_info_enclave_id != null_enclave_id) {
    result := monitor_invalid_value; return;
  }

  if (!assigned(eid) || !is_valid_enclave_id(enclave_metadata_valid, eid)) {
    result := monitor_invalid_value; return;
  }
  if (!enclave_metadata_valid[eid] ||
      !thread_metadata_valid[tid]  ||
      thread_metadata_eid[tid] != eid)
  {
    result := monitor_invalid_state; return;
  }
  if (!enclave_metadata_is_initialized[eid]) {
    result := monitor_invalid_state; return;
  }

  core_info_enclave_id := eid;
  core_info_thread_id := tid;
  cpu_evbase := enclave_metadata_ev_base[eid];
  cpu_evmask := enclave_metadata_ev_mask[eid];
  cpu_edrbmap := enclave_metadata_bitmap[eid];
  cpu_eptbr := enclave_metadata_load_eptbr[eid];
  // FIXME: cpu_ptbr? What happens to this?

  rip := thread_metadata_entry_pc[tid];

  result := monitor_ok;
}

procedure {:inline 1} exit_enclave()
  returns  (result: api_result_t)
  modifies core_info_enclave_id, rip;
{
  //must be called by OS
  if (core_info_enclave_id == null_enclave_id) {
    result := monitor_invalid_value; return;
  }

  core_info_enclave_id := null_enclave_id;
  rip := os_pc;
  result := monitor_ok;
}

procedure {:inline 1} block_dram_region(region: region_t)
  returns (result: api_result_t)
  modifies owner,
           enclave_metadata_bitmap,
           os_bitmap, cpu_drbmap,
           cpu_edrbmap, blocked_at,
           dram_regions_info_block_clock;
{
  if (!is_dynamic_dram_region(region)) {
    result := monitor_invalid_value; return;
  }

  if (owner[region] != core_info_enclave_id) {
    result := monitor_access_denied; return;
  }

  if (owner[region] == null_enclave_id) {
    os_bitmap := bitmap_clear_bit(os_bitmap, region);
    cpu_drbmap := os_bitmap;
  } else {
    enclave_metadata_bitmap[owner[region]] := bitmap_clear_bit(enclave_metadata_bitmap[owner[region]], region);
    cpu_edrbmap := enclave_metadata_bitmap[owner[region]];
  }

  owner[region] := blocked_enclave_id;
  blocked_at[region] := dram_regions_info_block_clock;
  dram_regions_info_block_clock := dram_regions_info_block_clock + 1;

  result := monitor_ok;
}

// Frees a DRAM region that was previously locked.
procedure {:inline 1} free_dram_region(region: region_t)
  returns (result: api_result_t)
  modifies owner, enclave_metadata_bitmap, os_bitmap, cpu_drbmap;
{
  if (!is_valid_dram_region(region)) {
    result := monitor_invalid_value; return;
  }

  //can only assign free dram regions
  if (owner[region] != blocked_enclave_id) {
    result := monitor_invalid_state; return;
  }

  if (core_flushed_at < blocked_at[region]) {
    //some TLBs are not flushed, and still refer to blocked regions
    result := monitor_invalid_state; return;
  }

  owner[region] := free_enclave_id;
  result := monitor_ok;
}

procedure {:inline 1} flush_cached_dram_regions()
  returns (result: api_result_t)
  modifies core_flushed_at;
{
  //must be called by OS
  if (core_info_enclave_id != null_enclave_id) {
    result := monitor_invalid_value; return;
  }

  //hardware TLB flush, which we won't model
  core_flushed_at := dram_regions_info_block_clock;
  result := monitor_ok;
}

procedure {:inline 1} delete_thread(tid: thread_id_t)
  returns (result: api_result_t)
  modifies thread_metadata_valid, enclave_metadata_thread_count;
{
  var eid: enclave_id_t;

  //must be called by OS
  if (core_info_enclave_id != null_enclave_id) {
    result := monitor_invalid_value; return;
  }

  eid := thread_metadata_eid[tid];

  if (!thread_metadata_valid[tid]) {
    result := monitor_invalid_value; return;
  }

  thread_metadata_valid[tid] := false;
  enclave_metadata_thread_count[eid] := enclave_metadata_thread_count[eid] - 1;
  result := monitor_ok;
}

procedure {:inline 1} delete_enclave(eid: enclave_id_t)
  returns (result: api_result_t)
  modifies enclave_metadata_valid, enclave_metadata_is_initialized, owner;
{
  var r: region_t;

  //must be called by OS
  if (core_info_enclave_id != null_enclave_id) {
    result := monitor_invalid_value; return;
  }

  if (!assigned(eid) || !enclave_metadata_valid[eid]) {
    result := monitor_invalid_value; return;
  }

  if (enclave_metadata_thread_count[eid] != 0) {
    result := monitor_invalid_state; return;
  }

  assert(assigned(eid));

  r := k0_region_t;
  while(LT_r(r, kN_region_t))
    invariant (forall ri: region_t :: LT_r(ri, r) ==> owner[ri] != eid);
    invariant (forall ri: region_t :: LT_r(ri, r) ==> (old(owner)[ri] != eid ==> old(owner)[ri] == owner[ri]));
  {
    if (owner[r] == eid) { result := monitor_invalid_state; return; }
    r := PLUS_r(r, k1_region_t);
  }

  if (owner[kN_region_t] == eid) { result := monitor_invalid_state; return; }
  assert (forall ri: region_t :: owner[ri] != eid);
  assert (forall ri: region_t :: (old(owner)[ri] != eid) ==> (old(owner)[ri] == owner[ri]));

  enclave_metadata_is_initialized[eid] := false;
  enclave_metadata_valid[eid] := false;

  result := monitor_ok;
}

//api_result_t set_dma_range(uintptr_t base, uintptr_t mask);
//api_result_t load_page(enclave_id_t enclave_id, uintptr_t phys_addr, uintptr_t virtual_addr, uintptr_t os_addr, uintptr_t acl);
