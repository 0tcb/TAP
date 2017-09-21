procedure TAPSanctumRefinement()
modifies cpu_enclave_id, cpu_addr_map, cpu_addr_valid, cpu_pc,
         cpu_regs, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr,
         cpu_drbmap, cpu_edrbmap, cpu_parbase, cpu_eparbase, cpu_parmask,
         cpu_eparmask, cpu_dmarbase, cpu_dmarmask,
         owner, cpu_owner_map, cpu_mem, mem,
         core_info_enclave_id, core_info_thread_id,
         thread_metadata_valid, os_bitmap,
         enclave_metadata_valid, enclave_metadata_is_initialized,
         enclave_metadata_ev_base, enclave_metadata_ev_mask,
         enclave_metadata_bitmap, enclave_metadata_thread_count,
         enclave_metadata_load_eptbr, enclave_metadata_dram_region_count,
         enclave_metadata_last_load_addr, enclave_metadata_measurement,
         thread_metadata_valid, thread_metadata_eid,
         thread_metadata_entry_pc, thread_metadata_entry_stack,
         thread_metadata_fault_pc, thread_metadata_fault_stack,
         enclave_metadata_thread_count, tap_enclave_metadata_valid,
         tap_enclave_metadata_addr_map, tap_enclave_metadata_addr_valid,
         tap_enclave_metadata_addr_excl, tap_enclave_metadata_entrypoint,
         tap_enclave_metadata_pc, tap_enclave_metadata_regs,
         tap_enclave_metadata_paused, tap_enclave_metadata_cache_conflict,
         cache_valid_map, cache_tag_map, rip, untrusted_regs,
         untrusted_addr_map, untrusted_addr_valid, untrusted_pc;
{
  assume cpu_ptbr == k2_ppn_t;
  assume cpu_parbase == 0bv9 ++ 0bv3 ++ 0bv12;
  assume cpu_parmask == 0bv9 ++ 0bv3 ++ 255bv12;
  assume cpu_eparbase == cpu_parbase;
  assume cpu_eparmask == cpu_parmask;
  assume cpu_dmarbase == 0bv9 ++ 0bv3 ++ 256bv12;
  assume cpu_dmarmask == 0bv9 ++ 0bv3 ++ 255bv12;
  assume (forall eid: enclave_id_t :: enclave_metadata_is_initialized[eid] ==> enclave_metadata_valid[eid]);
  assume (forall eid: enclave_id_t :: enclave_metadata_valid[eid] ==> assigned(eid));
  assume (forall eid: enclave_id_t :: enclave_metadata_valid[eid] ==> (owner[dram_region_for(eid)] == metadata_enclave_id));
  assume (forall r: region_t, e: enclave_id_t :: ((owner[r] == e) && assigned(e)) ==> enclave_metadata_valid[e]);
  assume (forall r: region_t, e: enclave_id_t :: ((owner[r] == e) && assigned(e)) ==> (owner[dram_region_for(e)] == metadata_enclave_id));
  assume (forall p: wap_addr_t :: (owner[dram_region_for_w(p)] == free_enclave_id) ==> (mem[p] == k0_word_t));
  assume (forall eid: enclave_id_t :: enclave_metadata_valid[eid] ==> (owner[dram_region_for(eid)] == metadata_enclave_id));
  assume (forall r: region_t, eid: enclave_id_t :: (enclave_metadata_valid[eid] && assigned(eid)) ==> (owner[r] == eid <==> AND_8(enclave_metadata_bitmap[eid], LSHIFT_8(1bv8, 0bv5 ++ r)) != 0bv8));
  assume (forall eid1, eid2: enclave_id_t :: (eid1 != eid2  && assigned(eid1) && assigned(eid2) && enclave_metadata_valid[eid1] && enclave_metadata_valid[eid2]) ==> (disjoint_bitmaps(enclave_metadata_bitmap[eid1], enclave_metadata_bitmap[eid2])));
  assume (forall eid: enclave_id_t :: (assigned(eid) && enclave_metadata_valid[eid]) ==> disjoint_bitmaps(enclave_metadata_bitmap[eid], os_bitmap));
  assume (forall r: region_t, e: enclave_id_t :: (enclave_metadata_valid[e] && assigned(e)) ==> (owner[r] != e ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
  assume (forall r: region_t, e: enclave_id_t :: enclave_metadata_valid[e] ==> (!assigned(owner[r]) ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
  assume (forall r: region_t :: ((owner[r] == null_enclave_id) ==> read_bitmap(os_bitmap, r) == 1bv1));
  assume (forall r: region_t :: ((owner[r] != null_enclave_id) ==> read_bitmap(os_bitmap, r) == 0bv1));
  assume (forall r: region_t, e : enclave_id_t :: ((owner[r] == e && assigned(e)) ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 1bv1)));
  assume (forall r: region_t, e : enclave_id_t :: ((owner[r] != e && assigned(e) && enclave_metadata_valid[e]) ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
  assume os_bitmap == cpu_drbmap;
  assume assigned(core_info_enclave_id) ==> (enclave_metadata_valid[core_info_enclave_id] && enclave_metadata_is_initialized[core_info_enclave_id]);
  assume assigned(core_info_enclave_id) ==> enclave_metadata_bitmap[core_info_enclave_id] == cpu_edrbmap;
  assume (forall e1: enclave_id_t, e2: enclave_id_t :: (enclave_metadata_is_initialized[e1] && enclave_metadata_is_initialized[e2] && e1 != e2) ==> (enclave_metadata_load_eptbr[e1] != enclave_metadata_load_eptbr[e2]));
  assume (forall e: enclave_id_t, r: region_t :: (enclave_metadata_valid[e] && enclave_metadata_is_initialized[e]) ==> (dram_region_for(enclave_metadata_load_eptbr[e] ++ 0bv12) == r ==> owner[r] == e));
  assume (core_info_enclave_id != blocked_enclave_id);
  assume core_info_enclave_id != null_enclave_id ==> (enclave_metadata_load_eptbr[core_info_enclave_id] == cpu_eptbr);
  assume core_info_enclave_id != null_enclave_id ==> (enclave_metadata_ev_base[core_info_enclave_id] == cpu_evbase);
  assume core_info_enclave_id != null_enclave_id ==> (enclave_metadata_ev_mask[core_info_enclave_id] == cpu_evmask);
  assume (cpu_enclave_id != tap_blocked_enc_id);
  assume (!tap_enclave_metadata_valid[tap_blocked_enc_id]);
  assume (cpu_enclave_id == tap_null_enc_id) ==> ((cpu_addr_map == untrusted_addr_map) && (forall v : vaddr_t :: tap_addr_perm_eq(cpu_addr_valid[v], untrusted_addr_valid[v])));
  assume (cpu_enclave_id != tap_null_enc_id) ==> (cpu_addr_map == tap_enclave_metadata_addr_map[cpu_enclave_id]);
  assume (cpu_enclave_id != tap_null_enc_id) ==> (forall v : vaddr_t :: tap_addr_perm_eq(cpu_addr_valid[v], tap_enclave_metadata_addr_valid[cpu_enclave_id][v]));
  assume (forall pa : wap_addr_t, e : tap_enclave_id_t :: (e != tap_null_enc_id && e != tap_blocked_enc_id && !tap_enclave_metadata_valid[e]) ==> (cpu_owner_map[pa] != e));
  assume (forall v : vaddr_t :: tap_addr_perm_r(cpu_addr_valid[v]) == acl2read(ptbl_acl_map[select_ppn(core_info_enclave_id, v, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(v)]));
  assume (forall v : vaddr_t :: tap_addr_perm_w(cpu_addr_valid[v]) == acl2write(ptbl_acl_map[select_ppn(core_info_enclave_id, v, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(v)]));
  assume (forall v : vaddr_t :: tap_addr_perm_x(cpu_addr_valid[v]) == acl2exec(ptbl_acl_map[select_ppn(core_info_enclave_id, v, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(v)]));
  assume cpu_enclave_id == enclave_id_bv2int(core_info_enclave_id);
  assume (cpu_enclave_id == tap_null_enc_id) <==> (core_info_enclave_id == null_enclave_id);
  assume ((cpu_enclave_id != tap_null_enc_id) ==> tap_enclave_metadata_valid[cpu_enclave_id]) && (core_info_enclave_id != null_enclave_id ==> enclave_metadata_valid[core_info_enclave_id]);
  assume (forall pa: wap_addr_t :: cpu_mem[pa] == mem[pa]);
  assume (forall eid: enclave_id_t :: enclave_metadata_is_initialized[eid] ==> tap_enclave_metadata_valid[enclave_id_bv2int(eid)]);
  assume (forall eid: enclave_id_t :: (enclave_metadata_is_initialized[eid] && enclave_metadata_valid[eid]) <==> tap_enclave_metadata_valid[enclave_id_bv2int(eid)]);
  assume (forall va: vaddr_t :: (untrusted_addr_map[va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va))));
  assume (forall va: vaddr_t, eid: enclave_id_t :: tap_enclave_metadata_valid[enclave_id_bv2int(eid)] ==> (if in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) then (tap_enclave_metadata_addr_map[enclave_id_bv2int(eid)][va] == paddr2wpaddr(ptbl_addr_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)] ++ vaddr2offset(va))) else (tap_enclave_metadata_addr_map[enclave_id_bv2int(eid)][va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va)))));
  assume (forall va : vaddr_t :: tap_addr_perm_r(untrusted_addr_valid[va]) == acl2read(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)]));
  assume (forall va : vaddr_t :: tap_addr_perm_w(untrusted_addr_valid[va]) == acl2write(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)]));
  assume (forall va : vaddr_t :: tap_addr_perm_x(untrusted_addr_valid[va]) == acl2exec(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)]));
  assume (forall va : vaddr_t :: tap_addr_perm_v(untrusted_addr_valid[va]) == acl2valid(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)]));
  assume (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_r(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2read(ptbl_acl_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)])));
  assume (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_w(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2write(ptbl_acl_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)])));
  assume (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_x(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2exec(ptbl_acl_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)])));
  assume (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_v(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2valid(ptbl_acl_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)])));
  assume (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && !in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_r(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2read(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])));
  assume (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && !in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_w(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2write(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])));
  assume (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && !in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_x(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2exec(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])));
  assume (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && !in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_v(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2valid(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])));
  assume (forall pa: wap_addr_t :: assigned(owner[dram_region_for_w(pa)]) ==> (enclave_metadata_is_initialized[owner[dram_region_for_w(pa)]] ==> (enclave_id_bv2int(owner[dram_region_for_w(pa)]) == cpu_owner_map[pa])));
  assume (forall pa: wap_addr_t :: (cpu_owner_map[pa] == tap_null_enc_id) <==> (owner[dram_region_for_w(pa)] == null_enclave_id));
  assume (forall pa: wap_addr_t :: (cpu_owner_map[pa] == tap_blocked_enc_id) <==> (owner[dram_region_for_w(pa)] == blocked_enclave_id));
  assume (forall pa: wap_addr_t :: (cpu_owner_map[pa] != tap_null_enc_id && cpu_owner_map[pa] != tap_blocked_enc_id) ==> (enclave_id_bv2int(owner[dram_region_for_w(pa)]) == cpu_owner_map[pa]));
  assume (forall pa: wap_addr_t :: (owner[dram_region_for_w(pa)] == null_enclave_id) <==> (tap_null_enc_id == cpu_owner_map[pa]));
  assume (forall pa: wap_addr_t :: !assigned(owner[dram_region_for_w(pa)]) <==> (tap_null_enc_id == cpu_owner_map[pa] || tap_blocked_enc_id == cpu_owner_map[pa]));
  assume (forall pa: wap_addr_t :: (read_bitmap(os_bitmap, dram_region_for_w(pa)) == 1bv1) <==> (cpu_owner_map[pa] == tap_null_enc_id));
  while (*)
    invariant cpu_ptbr == k2_ppn_t;
    invariant cpu_parbase == 0bv9 ++ 0bv3 ++ 0bv12;
    invariant cpu_parmask == 0bv9 ++ 0bv3 ++ 255bv12;
    invariant cpu_eparbase == cpu_parbase;
    invariant cpu_eparmask == cpu_parmask;
    invariant cpu_dmarbase == 0bv9 ++ 0bv3 ++ 256bv12;
    invariant cpu_dmarmask == 0bv9 ++ 0bv3 ++ 255bv12;
    invariant (forall eid: enclave_id_t :: enclave_metadata_is_initialized[eid] ==> enclave_metadata_valid[eid]);
    invariant (forall eid: enclave_id_t :: enclave_metadata_valid[eid] ==> assigned(eid));
    invariant (forall eid: enclave_id_t :: enclave_metadata_valid[eid] ==> (owner[dram_region_for(eid)] == metadata_enclave_id));
    invariant (forall r: region_t, e: enclave_id_t :: ((owner[r] == e) && assigned(e)) ==> enclave_metadata_valid[e]);
    invariant (forall r: region_t, e: enclave_id_t :: ((owner[r] == e) && assigned(e)) ==> (owner[dram_region_for(e)] == metadata_enclave_id));
    invariant (forall p: wap_addr_t :: (owner[dram_region_for_w(p)] == free_enclave_id) ==> (mem[p] == k0_word_t));
    invariant (forall eid: enclave_id_t :: enclave_metadata_valid[eid] ==> (owner[dram_region_for(eid)] == metadata_enclave_id));
    invariant (forall r: region_t, eid: enclave_id_t :: (enclave_metadata_valid[eid] && assigned(eid)) ==> (owner[r] == eid <==> AND_8(enclave_metadata_bitmap[eid], LSHIFT_8(1bv8, 0bv5 ++ r)) != 0bv8));
    invariant (forall eid1, eid2: enclave_id_t :: (eid1 != eid2  && assigned(eid1) && assigned(eid2) && enclave_metadata_valid[eid1] && enclave_metadata_valid[eid2]) ==> (disjoint_bitmaps(enclave_metadata_bitmap[eid1], enclave_metadata_bitmap[eid2])));
    invariant (forall eid: enclave_id_t :: (assigned(eid) && enclave_metadata_valid[eid]) ==> disjoint_bitmaps(enclave_metadata_bitmap[eid], os_bitmap));
    invariant (forall r: region_t, e: enclave_id_t :: (enclave_metadata_valid[e] && assigned(e)) ==> (owner[r] != e ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
    invariant (forall r: region_t, e: enclave_id_t :: enclave_metadata_valid[e] ==> (!assigned(owner[r]) ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
    invariant (forall r: region_t :: ((owner[r] == null_enclave_id) ==> read_bitmap(os_bitmap, r) == 1bv1));
    invariant (forall r: region_t :: ((owner[r] != null_enclave_id) ==> read_bitmap(os_bitmap, r) == 0bv1));
    invariant (forall r: region_t, e : enclave_id_t :: ((owner[r] == e && assigned(e)) ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 1bv1)));
    invariant (forall r: region_t, e : enclave_id_t :: ((owner[r] != e && assigned(e) && enclave_metadata_valid[e]) ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
    invariant os_bitmap == cpu_drbmap;
    invariant assigned(core_info_enclave_id) ==> (enclave_metadata_valid[core_info_enclave_id] && enclave_metadata_is_initialized[core_info_enclave_id]);
    invariant assigned(core_info_enclave_id) ==> enclave_metadata_bitmap[core_info_enclave_id] == cpu_edrbmap;
    invariant (forall e1: enclave_id_t, e2: enclave_id_t :: (enclave_metadata_is_initialized[e1] && enclave_metadata_is_initialized[e2] && e1 != e2) ==> (enclave_metadata_load_eptbr[e1] != enclave_metadata_load_eptbr[e2]));
    invariant (forall e: enclave_id_t, r: region_t :: (enclave_metadata_valid[e] && enclave_metadata_is_initialized[e]) ==> (dram_region_for(enclave_metadata_load_eptbr[e] ++ 0bv12) == r ==> owner[r] == e));
    invariant (core_info_enclave_id != blocked_enclave_id);
    invariant core_info_enclave_id != null_enclave_id ==> (enclave_metadata_load_eptbr[core_info_enclave_id] == cpu_eptbr);
    invariant core_info_enclave_id != null_enclave_id ==> (enclave_metadata_ev_base[core_info_enclave_id] == cpu_evbase);
    invariant core_info_enclave_id != null_enclave_id ==> (enclave_metadata_ev_mask[core_info_enclave_id] == cpu_evmask);
    invariant (cpu_enclave_id != tap_blocked_enc_id);
    invariant (!tap_enclave_metadata_valid[tap_blocked_enc_id]);
    invariant (cpu_enclave_id == tap_null_enc_id) ==> ((cpu_addr_map == untrusted_addr_map) && (forall v : vaddr_t :: tap_addr_perm_eq(cpu_addr_valid[v], untrusted_addr_valid[v])));
    invariant (cpu_enclave_id != tap_null_enc_id) ==> (cpu_addr_map == tap_enclave_metadata_addr_map[cpu_enclave_id]);
    invariant (cpu_enclave_id != tap_null_enc_id) ==> (forall v : vaddr_t :: tap_addr_perm_eq(cpu_addr_valid[v], tap_enclave_metadata_addr_valid[cpu_enclave_id][v]));
    invariant (forall pa : wap_addr_t, e : tap_enclave_id_t :: (e != tap_null_enc_id && e != tap_blocked_enc_id && !tap_enclave_metadata_valid[e]) ==> (cpu_owner_map[pa] != e));
    invariant (forall v : vaddr_t :: tap_addr_perm_r(cpu_addr_valid[v]) == acl2read(ptbl_acl_map[select_ppn(core_info_enclave_id, v, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(v)]));
    invariant (forall v : vaddr_t :: tap_addr_perm_w(cpu_addr_valid[v]) == acl2write(ptbl_acl_map[select_ppn(core_info_enclave_id, v, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(v)]));
    invariant (forall v : vaddr_t :: tap_addr_perm_x(cpu_addr_valid[v]) == acl2exec(ptbl_acl_map[select_ppn(core_info_enclave_id, v, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(v)]));
    invariant cpu_enclave_id == enclave_id_bv2int(core_info_enclave_id);
    invariant (cpu_enclave_id == tap_null_enc_id) <==> (core_info_enclave_id == null_enclave_id);
    invariant ((cpu_enclave_id != tap_null_enc_id) ==> tap_enclave_metadata_valid[cpu_enclave_id]) && (core_info_enclave_id != null_enclave_id ==> enclave_metadata_valid[core_info_enclave_id]);
    invariant (forall pa: wap_addr_t :: cpu_mem[pa] == mem[pa]);
    invariant (forall eid: enclave_id_t :: enclave_metadata_is_initialized[eid] ==> tap_enclave_metadata_valid[enclave_id_bv2int(eid)]);
    invariant (forall eid: enclave_id_t :: (enclave_metadata_is_initialized[eid] && enclave_metadata_valid[eid]) <==> tap_enclave_metadata_valid[enclave_id_bv2int(eid)]);
    invariant (forall va: vaddr_t :: (untrusted_addr_map[va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va))));
    invariant (forall va: vaddr_t, eid: enclave_id_t :: tap_enclave_metadata_valid[enclave_id_bv2int(eid)] ==> (if in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) then (tap_enclave_metadata_addr_map[enclave_id_bv2int(eid)][va] == paddr2wpaddr(ptbl_addr_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)] ++ vaddr2offset(va))) else (tap_enclave_metadata_addr_map[enclave_id_bv2int(eid)][va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va)))));
    invariant (forall va : vaddr_t :: tap_addr_perm_r(untrusted_addr_valid[va]) == acl2read(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)]));
    invariant (forall va : vaddr_t :: tap_addr_perm_w(untrusted_addr_valid[va]) == acl2write(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)]));
    invariant (forall va : vaddr_t :: tap_addr_perm_x(untrusted_addr_valid[va]) == acl2exec(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)]));
    invariant (forall va : vaddr_t :: tap_addr_perm_v(untrusted_addr_valid[va]) == acl2valid(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)]));
    invariant (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_r(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2read(ptbl_acl_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)])));
    invariant (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_w(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2write(ptbl_acl_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)])));
    invariant (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_x(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2exec(ptbl_acl_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)])));
    invariant (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_v(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2valid(ptbl_acl_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)])));
    invariant (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && !in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_r(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2read(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])));
    invariant (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && !in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_w(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2write(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])));
    invariant (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && !in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_x(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2exec(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])));
    invariant (forall va: vaddr_t, eid: enclave_id_t :: (tap_enclave_metadata_valid[enclave_id_bv2int(eid)] && !in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])) ==> (tap_addr_perm_v(tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va]) == acl2valid(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])));
    invariant (forall pa: wap_addr_t :: assigned(owner[dram_region_for_w(pa)]) ==> (enclave_metadata_is_initialized[owner[dram_region_for_w(pa)]] ==> (enclave_id_bv2int(owner[dram_region_for_w(pa)]) == cpu_owner_map[pa])));
    invariant (forall pa: wap_addr_t :: (cpu_owner_map[pa] == tap_null_enc_id) <==> (owner[dram_region_for_w(pa)] == null_enclave_id));
    invariant (forall pa: wap_addr_t :: (cpu_owner_map[pa] == tap_blocked_enc_id) <==> (owner[dram_region_for_w(pa)] == blocked_enclave_id));
    invariant (forall pa: wap_addr_t :: (cpu_owner_map[pa] != tap_null_enc_id && cpu_owner_map[pa] != tap_blocked_enc_id) ==> (enclave_id_bv2int(owner[dram_region_for_w(pa)]) == cpu_owner_map[pa]));
    invariant (forall pa: wap_addr_t :: (owner[dram_region_for_w(pa)] == null_enclave_id) <==> (tap_null_enc_id == cpu_owner_map[pa]));
    invariant (forall pa: wap_addr_t :: !assigned(owner[dram_region_for_w(pa)]) <==> (tap_null_enc_id == cpu_owner_map[pa] || tap_blocked_enc_id == cpu_owner_map[pa]));
    invariant (forall pa: wap_addr_t :: (read_bitmap(os_bitmap, dram_region_for_w(pa)) == 1bv1) <==> (cpu_owner_map[pa] == tap_null_enc_id));
  {
    if (*) {
      call refinement_proof_step_load();
    } else if (*) {
      call refinement_proof_step_store();
    } else if (*) {
      call refinement_proof_step_create_metadata_region();
    } else if (*) {
      call refinement_proof_step_create_enclave();
    } else if (*) {
      call refinement_proof_step_assign_dram_region();
    } else if (*) {
       call refinement_proof_step_free_dram_region();
    } else if (*) {
      call refinement_proof_step_load_thread();
    } else if (*) {
      call refinement_proof_step_delete_thread();
    } else if (*) {
      call refinement_proof_step_launch();
    } else if (*) {
      call refinement_proof_step_enter_enclave();
    } else if (*) {
      call refinement_proof_step_exit_enclave();
    } else if (*) {
      call refinement_proof_step_delete_enclave();
    }
  }
}
