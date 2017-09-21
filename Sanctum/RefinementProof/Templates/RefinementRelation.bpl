assert cpu_ptbr == k2_ppn_t;
assert cpu_parbase == 0bv9 ++ 0bv3 ++ 0bv12;
assert cpu_parmask == 0bv9 ++ 0bv3 ++ 255bv12;
assert cpu_eparbase == cpu_parbase;
assert cpu_eparmask == cpu_parmask;
assert cpu_dmarbase == 0bv9 ++ 0bv3 ++ 256bv12;
assert cpu_dmarmask == 0bv9 ++ 0bv3 ++ 255bv12;
assert (forall eid: enclave_id_t :: enclave_metadata_is_initialized[eid] ==> enclave_metadata_valid[eid]);
assert (forall eid: enclave_id_t :: enclave_metadata_valid[eid] ==> assigned(eid));
assert (forall eid: enclave_id_t ::
      enclave_metadata_valid[eid] ==> (owner[dram_region_for(eid)] == metadata_enclave_id));
assert (forall r: region_t, e: enclave_id_t ::
      ((owner[r] == e) && assigned(e)) ==> enclave_metadata_valid[e]);
assert (forall r: region_t, e: enclave_id_t ::
      ((owner[r] == e) && assigned(e)) ==> (owner[dram_region_for(e)] == metadata_enclave_id));
assert (forall p: wap_addr_t :: (owner[dram_region_for_w(p)] == free_enclave_id) ==> (mem[p] == k0_word_t));
assert (forall eid: enclave_id_t :: enclave_metadata_valid[eid] ==> (owner[dram_region_for(eid)] == metadata_enclave_id));
assert (forall r: region_t, eid: enclave_id_t :: (enclave_metadata_valid[eid] && assigned(eid)) ==>
      (owner[r] == eid <==> AND_8(enclave_metadata_bitmap[eid], LSHIFT_8(1bv8, 0bv5 ++ r)) != 0bv8));
assert (forall eid1, eid2: enclave_id_t ::
                (eid1 != eid2  && assigned(eid1) && assigned(eid2) && enclave_metadata_valid[eid1] && enclave_metadata_valid[eid2]) ==>
                (disjoint_bitmaps(enclave_metadata_bitmap[eid1], enclave_metadata_bitmap[eid2])));
assert (forall eid: enclave_id_t ::
                (assigned(eid) && enclave_metadata_valid[eid]) ==> disjoint_bitmaps(enclave_metadata_bitmap[eid], os_bitmap));
assert (forall r: region_t, e: enclave_id_t :: (enclave_metadata_valid[e] && assigned(e)) ==>
        (owner[r] != e ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
assert (forall r: region_t, e: enclave_id_t :: enclave_metadata_valid[e] ==>
        (!assigned(owner[r]) ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
assert (forall r: region_t :: ((owner[r] == null_enclave_id) ==> read_bitmap(os_bitmap, r) == 1bv1));
assert (forall r: region_t :: ((owner[r] != null_enclave_id) ==> read_bitmap(os_bitmap, r) == 0bv1));
assert (forall r: region_t, e : enclave_id_t :: ((owner[r] == e && assigned(e)) ==>
      (read_bitmap(enclave_metadata_bitmap[e], r) == 1bv1)));
assert (forall r: region_t, e : enclave_id_t :: ((owner[r] != e && assigned(e) && enclave_metadata_valid[e]) ==>
      (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
assert os_bitmap == cpu_drbmap;
assert assigned(core_info_enclave_id) || (core_info_enclave_id == null_enclave_id);
assert assigned(core_info_enclave_id) ==> (enclave_metadata_valid[core_info_enclave_id] && enclave_metadata_is_initialized[core_info_enclave_id]);
assert assigned(core_info_enclave_id) ==> enclave_metadata_bitmap[core_info_enclave_id] == cpu_edrbmap;
assert (forall e1: enclave_id_t, e2: enclave_id_t :: (enclave_metadata_is_initialized[e1] && enclave_metadata_is_initialized[e2] && e1 != e2) ==>
      (enclave_metadata_load_eptbr[e1] != enclave_metadata_load_eptbr[e2]));
assert (forall e: enclave_id_t, r: region_t :: (enclave_metadata_valid[e] && enclave_metadata_is_initialized[e]) ==>
      (dram_region_for(enclave_metadata_load_eptbr[e] ++ 0bv12) == r ==> owner[r] == e));
// we never use the blocked enclave id.
assert (core_info_enclave_id != blocked_enclave_id);
// Sanctum monitor metadata is consistent with CPU registers.
assert core_info_enclave_id != null_enclave_id ==> (enclave_metadata_load_eptbr[core_info_enclave_id] == cpu_eptbr);
assert core_info_enclave_id != null_enclave_id ==> (enclave_metadata_ev_base[core_info_enclave_id] == cpu_evbase);
assert core_info_enclave_id != null_enclave_id ==> (enclave_metadata_ev_mask[core_info_enclave_id] == cpu_evmask);

// TAP's invariants next
assert (cpu_enclave_id != tap_blocked_enc_id);
assert (!tap_enclave_metadata_valid[tap_blocked_enc_id]);
assert (cpu_enclave_id == tap_null_enc_id) ==> ((cpu_addr_map == untrusted_addr_map) && (forall v : vaddr_t :: tap_perm_eq(cpu_addr_valid[v], untrusted_addr_valid[v])));
assert (cpu_enclave_id != tap_null_enc_id) ==> (cpu_addr_map == tap_enclave_metadata_addr_map[cpu_enclave_id]);
assert (cpu_enclave_id != tap_null_enc_id) ==> (forall v : vaddr_t :: tap_perm_eq(cpu_addr_valid[v], tap_enclave_metadata_addr_valid[cpu_enclave_id][v]));
assert (forall pa : wap_addr_t, e : tap_enclave_id_t :: 
            (e != tap_null_enc_id && e != tap_blocked_enc_id && e != tap_metadata_enc_id && !tap_enclave_metadata_valid[e]) ==> 
            (cpu_owner_map[pa] != e));
// permissions are the same for each vaddr.
// not enclave.
assert (forall va: vaddr_t, vpn : vpn_t :: 
         (core_info_enclave_id == null_enclave_id               &&
          cpu_enclave_id == tap_null_enc_id                     &&
          vpn == vaddr2vpn(va))
         ==>
          tap_sanctum_perm_eq(cpu_addr_valid[va], ptbl_acl_map[cpu_ptbr, vpn]));
assert (forall va: vaddr_t, vpn : vpn_t :: 
         (core_info_enclave_id == null_enclave_id            &&
          cpu_enclave_id == tap_null_enc_id                  &&
          vpn == vaddr2vpn(va))
         ==>
          (cpu_addr_map[va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vpn] ++ vaddr2offset(va))));
// evrange is the same.
assert (forall va: vaddr_t, vpn : vpn_t :: 
         (core_info_enclave_id != null_enclave_id && cpu_enclave_id != tap_null_enc_id) ==>
         (in_enclave_mem(va, cpu_evbase, cpu_evmask) <==> tap_enclave_metadata_addr_excl[cpu_enclave_id][va]));
// inside evrange.
assert (forall va: vaddr_t, vpn : vpn_t :: 
         (core_info_enclave_id != null_enclave_id               &&
          cpu_enclave_id != tap_null_enc_id                     &&
          enclave_metadata_is_initialized[core_info_enclave_id] &&
          tap_enclave_metadata_valid[cpu_enclave_id]            &&
          vpn == vaddr2vpn(va)                                  && 
          in_enclave_mem(va, cpu_evbase, cpu_evmask)            &&
          tap_enclave_metadata_addr_excl[cpu_enclave_id][va])
         ==>
          tap_sanctum_perm_eq(cpu_addr_valid[va], ptbl_acl_map[cpu_eptbr, vpn]));
assert (forall va: vaddr_t, vpn : vpn_t :: 
         (core_info_enclave_id != null_enclave_id               &&
          cpu_enclave_id != tap_null_enc_id                     &&
          vpn == vaddr2vpn(va)                                  && 
          enclave_metadata_is_initialized[core_info_enclave_id] &&
          tap_enclave_metadata_valid[cpu_enclave_id]            &&
          in_enclave_mem(va, cpu_evbase, cpu_evmask)            &&
          tap_enclave_metadata_addr_excl[cpu_enclave_id][va])
         ==>
          (cpu_addr_map[va] == paddr2wpaddr(ptbl_addr_map[cpu_eptbr, vpn] ++ vaddr2offset(va))));
// outside evrange.
assert (forall va: vaddr_t, vpn : vpn_t :: 
         (core_info_enclave_id != null_enclave_id               &&
          cpu_enclave_id != tap_null_enc_id                     &&
          vpn == vaddr2vpn(va)                                  && 
          enclave_metadata_is_initialized[core_info_enclave_id] &&
          tap_enclave_metadata_valid[cpu_enclave_id]            &&
          !in_enclave_mem(va, cpu_evbase, cpu_evmask)           &&
          !tap_enclave_metadata_addr_excl[cpu_enclave_id][va])
         ==>
          tap_sanctum_perm_eq(cpu_addr_valid[va], ptbl_acl_map[cpu_ptbr, vpn]));
assert (forall va: vaddr_t, vpn : vpn_t :: 
         (core_info_enclave_id != null_enclave_id               &&
          cpu_enclave_id != tap_null_enc_id                     &&
          vpn == vaddr2vpn(va)                                  && 
          enclave_metadata_is_initialized[core_info_enclave_id] &&
          tap_enclave_metadata_valid[cpu_enclave_id]            &&
          !in_enclave_mem(va, cpu_evbase, cpu_evmask)           &&
          !tap_enclave_metadata_addr_excl[cpu_enclave_id][va])
         ==>
          (cpu_addr_map[va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vpn] ++ vaddr2offset(va))));
// current enclave_ids are related
assert cpu_enclave_id == enclave_id_bv2int(core_info_enclave_id);
assert (cpu_enclave_id == tap_null_enc_id) <==> (core_info_enclave_id == null_enclave_id);
assert ((cpu_enclave_id != tap_null_enc_id) ==> tap_enclave_metadata_valid[cpu_enclave_id]) &&
          (core_info_enclave_id != null_enclave_id ==> enclave_metadata_valid[core_info_enclave_id]);
// memories are related
assert (forall pa: wap_addr_t :: cpu_mem[pa] == mem[pa]);

// metadata_valid maps are related
assert (forall eid: enclave_id_t :: enclave_metadata_is_initialized[eid] <==> tap_enclave_metadata_valid[enclave_id_bv2int(eid)]);
//assert (forall eid: enclave_id_t :: (enclave_metadata_is_initialized[eid] && enclave_metadata_valid[eid]) <==> tap_enclave_metadata_valid[enclave_id_bv2int(eid)]);

// page tables are related
assert (forall va: vaddr_t ::
      (untrusted_addr_map[va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va))));
assert (forall va: vaddr_t, eid: enclave_id_t :: tap_enclave_metadata_valid[enclave_id_bv2int(eid)] ==>
      (if in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid])
          then (tap_enclave_metadata_addr_map[enclave_id_bv2int(eid)][va] == paddr2wpaddr(ptbl_addr_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)] ++ vaddr2offset(va))) 
          else (tap_enclave_metadata_addr_map[enclave_id_bv2int(eid)][va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va)))));
// permissions are the same in TAP and Sanctum for the adversary (OS).
assert (forall va : vaddr_t :: tap_sanctum_perm_eq(untrusted_addr_valid[va], ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])); 
// assert (forall va : vaddr_t :: tap_addr_perm_r(untrusted_addr_valid[va]) == acl2read(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])); 
// assert (forall va : vaddr_t :: tap_addr_perm_w(untrusted_addr_valid[va]) == acl2write(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])); 
// assert (forall va : vaddr_t :: tap_addr_perm_x(untrusted_addr_valid[va]) == acl2exec(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])); 
// assert (forall va : vaddr_t :: tap_addr_perm_v(untrusted_addr_valid[va]) == acl2valid(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])); 

// evrange is the same for both.
assert (forall eid: enclave_id_t, va:vaddr_t :: 
    (enclave_metadata_is_initialized[eid] && 
     tap_enclave_metadata_valid[enclave_id_bv2int(eid)]) 
    ==> 
    (in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) <==> 
     tap_enclave_metadata_addr_excl[enclave_id_bv2int(eid)][va]));
// permissions are the same in TAP and Sanctum for the enclaves.
// these refer to memory within evrange.
assert (forall va: vaddr_t, eid: enclave_id_t, t_eid : tap_enclave_id_t, vpn : vpn_t, eptbr : ppn_t :: 
         (t_eid == enclave_id_bv2int(eid)                                                  &&
          vpn == vaddr2vpn(va)                                                             && 
          eptbr == enclave_metadata_load_eptbr[eid]                                        &&
          enclave_metadata_is_initialized[eid]                                             &&
          tap_enclave_metadata_valid[t_eid]                                                &&
          in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) &&
          tap_enclave_metadata_addr_excl[t_eid][va])
         ==>
          tap_sanctum_perm_eq(tap_enclave_metadata_addr_valid[t_eid][va], ptbl_acl_map[eptbr, vpn]));
// these refer to addresses outside evrange.
assert (forall va: vaddr_t, eid: enclave_id_t, t_eid : tap_enclave_id_t, vpn : vpn_t :: 
         (t_eid == enclave_id_bv2int(eid)                                                   &&
          vpn == vaddr2vpn(va)                                                              && 
          enclave_metadata_is_initialized[eid]                                              &&
          tap_enclave_metadata_valid[t_eid]                                                 &&
          !in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) &&
          !tap_enclave_metadata_addr_excl[t_eid][va])
         ==>
          tap_sanctum_perm_eq(tap_enclave_metadata_addr_valid[t_eid][va], ptbl_acl_map[cpu_ptbr, vpn]));
// Sanctum's owner map is related to TAP's owner map
assert (forall pa: wap_addr_t, eid : enclave_id_t :: enclave_metadata_is_initialized[eid] ==>
            (owner[dram_region_for_w(pa)] == eid <==> (cpu_owner_map[pa] == enclave_id_bv2int(eid))));
assert (forall pa: wap_addr_t, eid : enclave_id_t :: (assigned(eid) && !enclave_metadata_is_initialized[eid]) ==>
            (owner[dram_region_for_w(pa)] == eid ==> (cpu_owner_map[pa] == tap_null_enc_id)));
assert (forall pa: wap_addr_t :: 
            (owner[dram_region_for_w(pa)] == null_enclave_id) ==> (tap_null_enc_id == cpu_owner_map[pa]));
assert (forall pa: wap_addr_t :: 
            (owner[dram_region_for_w(pa)] == free_enclave_id) ==> (tap_null_enc_id == cpu_owner_map[pa]));
assert (forall pa: wap_addr_t :: 
            (owner[dram_region_for_w(pa)] == metadata_enclave_id) <==> (tap_metadata_enc_id == cpu_owner_map[pa]));
assert (forall pa: wap_addr_t :: 
            (owner[dram_region_for_w(pa)] == blocked_enclave_id) <==> (tap_blocked_enc_id == cpu_owner_map[pa]));

// Sanctum's bitmaps are related to TAP's owner maps
assert (forall pa: wap_addr_t :: (read_bitmap(os_bitmap, dram_region_for_w(pa)) == 1bv1) ==> (cpu_owner_map[pa] == tap_null_enc_id));
assert (forall pa: wap_addr_t, e: enclave_id_t :: (enclave_metadata_valid[e] && assigned(e)) ==>
      ((read_bitmap(enclave_metadata_bitmap[e], dram_region_for_w(pa)) == 1bv1) <==> (cpu_owner_map[pa] == enclave_id_bv2int(e))));
