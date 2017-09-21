implementation initialize_sanctum()
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
  os_bitmap := 1bv8; //OS owns regions {0}

  enclave_metadata_valid := enclave_metadata_valid_init;
  havoc enclave_metadata_is_initialized;
  assume (forall e : enclave_id_t :: !enclave_metadata_is_initialized[e]);
  thread_metadata_valid := thread_metadata_valid_init;
  mem := mem_zero;

}

implementation _clear_mapped_pages(ptbr : ppn_t)
{
  var vpn : vpn_t;
  vpn := k0_vpn_t;
  while (LT_vpn(vpn, kmax_vpn_t))
    invariant (forall v : vpn_t :: 
      LT_vpn(v, vpn) ==> (ptbl_acl_map[ptbr, v] == k_pg_invalid_acl));
    invariant (forall p : ppn_t, v : vpn_t ::
      (p != ptbr) ==> (ptbl_acl_map[p, v] == old(ptbl_acl_map)[p, v]));
  {
    ptbl_acl_map[ptbr, vpn] := k_pg_invalid_acl;
    vpn := PLUS_vpn(vpn, k1_vpn_t);
  }
  ptbl_acl_map[ptbr, vpn] := k_pg_invalid_acl;
  vpn := PLUS_vpn(vpn, k1_vpn_t);
}

implementation _clear_page(ppn : ppn_t)
{
  var paddr : wap_addr_t;
  var ind : wpoffset_t;

  ind := k0_wpoffset_t;
  while (LT_wpo(ind, kN_wpoffset_t))
    invariant (forall pa : wap_addr_t :: 
                  wpaddr2ppn(pa) != ppn ==> mem[pa] == old(mem)[pa]);
    invariant (forall pa : wap_addr_t ::
                  if (wpaddr2ppn(pa) == ppn && LT_wpo(wpaddr2offset(pa), ind)) 
                      then mem[pa] == k0_word_t
                      else mem[pa] == old(mem)[pa]);
  {
    paddr := ppn ++ ind;
    mem[paddr] := k0_word_t;
    ind := PLUS_wpo(ind, k1_wpoffset_t);
  }
  paddr := ppn ++ ind;
  mem[paddr] := k0_word_t;
}

implementation load_page_impl(eid: enclave_id_t, vaddr: vaddr_t, src_paddr : paddr_t)
  returns (result: api_result_t)
{
  var src_wpaddr : wap_addr_t;
  var dst_wpaddr : wap_addr_t;
  var ptbr       : ppn_t;
  var src_vpn    : vpn_t;
  var src_ppn    : ppn_t;
  var dst_ppn    : ppn_t;
  var acl        : pte_acl_t;
  var evbase     : vaddr_t;
  var evmask     : vaddr_t;
  var po         : wpoffset_t;

  // must be called by OS.
  if (core_info_enclave_id != null_enclave_id) {
    result := monitor_invalid_value; return;
  }

  // vaddr must page aligned
  if (!is_page_aligned_va(vaddr)) {
    result := monitor_invalid_value; return;
  }

  if (!is_dram_address(src_paddr)) {
    result := monitor_invalid_value; return;
  }

  if (!is_page_aligned_pa(src_paddr)) {
    result := monitor_invalid_value; return;
  }

  // valid enclave?
  if (eid == null_enclave_id || !is_valid_enclave_id(enclave_metadata_valid, eid)) {
    result := monitor_invalid_value;
    return;
  }

  // enclave initialized?
  if (enclave_metadata_is_initialized[eid]) {
    result := monitor_invalid_state;
    return;
  }

  // vaddr must be inside evrange.
  evbase := enclave_metadata_ev_base[eid];
  evmask := enclave_metadata_ev_mask[eid];
  if (!is_in_evrange(evbase, evmask, vaddr)) {
    result := monitor_invalid_state;
    return;
  }

  // page table not initialized?
  ptbr := enclave_metadata_load_eptbr[eid];
  if (ptbr == k0_ppn_t) {
    result := monitor_invalid_state;
    return;
  }

  // page table entry must be mapped.
  src_vpn := vaddr2vpn(vaddr);
  acl := ptbl_acl_map[ptbr, src_vpn];
  if (!acl2valid(acl)) {
    result := monitor_invalid_value;
    return;
  }

  // copy data from src page to dst page.
  dst_ppn := ptbl_addr_map[ptbr, src_vpn];
  src_ppn := paddr2ppn(src_paddr);
  po := k0_wpoffset_t;
  while (LT_wpo(po, kN_wpoffset_t))
    invariant (forall p : wap_addr_t ::
      if (wpaddr2ppn(p) == dst_ppn && LT_wpo(wpaddr2offset(p), po)) 
          then (mem[p] == mem[src_ppn ++ wpaddr2offset(p)])
          else (mem[p] == old(mem)[p]));
  {
    dst_wpaddr := dst_ppn ++ po;
    src_wpaddr := src_ppn ++ po;
    mem[dst_wpaddr] := mem[src_wpaddr];
    po := PLUS_wpo(po, k1_wpoffset_t);
  }
  dst_wpaddr := dst_ppn ++ po;
  src_wpaddr := src_ppn ++ po;
  mem[dst_wpaddr] := mem[src_wpaddr];
  // reset dst_wpaddr
  dst_wpaddr := dst_ppn ++ k0_wpoffset_t;
  // we have succeeded!
  result := monitor_ok;
}

implementation delete_enclave(eid: enclave_id_t)
  returns (result: api_result_t)
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
    invariant (forall ri: region_t :: 
                if LT_r(ri, r) && old(owner)[ri] == eid
                    then owner[ri] == blocked_enclave_id
                    else owner[ri] == old(owner)[ri]);
  {
    if (owner[r] == eid) { owner[r] := blocked_enclave_id; }
    r := PLUS_r(r, k1_region_t);
  }
  if (owner[kN_region_t] == eid) { 
    owner[r] := blocked_enclave_id; 
  }
  assert (forall ri: region_t :: owner[ri] != eid);
  assert (forall ri: region_t :: 
            (if old(owner)[ri] == eid
                then owner[ri] == blocked_enclave_id
                else owner[ri] == old(owner)[ri]));

  enclave_metadata_is_initialized[eid] := false;
  enclave_metadata_valid[eid] := false;

  result := monitor_ok;
}

procedure _clear_dram_region(region: region_t);
  modifies mem;
  ensures (forall p : wap_addr_t :: 
            if dram_region_for_w(p) == region 
                then mem[p] == k0_word_t
                else mem[p] == old(mem)[p]);

implementation free_dram_region(region: region_t)
  returns (result: api_result_t)
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
  
  call _clear_dram_region(region);
  owner[region] := free_enclave_id;
  result := monitor_ok;
}
