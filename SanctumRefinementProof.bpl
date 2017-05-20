
function {:inline} disjoint_bitmaps(b1: bv8, b2: bv8) : bool { AND_8(b1, b2) == 0bv8 }

function {:inline} acl2addrperm(acl : pte_acl_t) : addr_perm_t
{ acl[3:2] ++ acl[2:1] ++ acl[4:3] ++ 0bv1 ++ acl[1:0] }

function {:inline} enclave_id_bv2int(input: enclave_id_t): tap_enclave_id_t;
axiom (forall v1, v2 : enclave_id_t :: v1 != v2 ==> enclave_id_bv2int(v1) != enclave_id_bv2int(v2));
axiom (forall v1 : enclave_id_t :: v1 == null_enclave_id ==> enclave_id_bv2int(v1) == tap_null_enc_id);

procedure TAPSanctumRefinement()
modifies cpu_enclave_id,
         cpu_addr_map,
         cpu_addr_valid,
         cpu_pc,
         cpu_regs,
         cpu_evbase,
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
         cpu_owner_map,
         cpu_mem,
         mem,
         core_info_enclave_id,
         core_info_thread_id,
         thread_metadata_valid,
         os_bitmap,
         enclave_metadata_valid,
         enclave_metadata_is_initialized,
         enclave_metadata_ev_base,
         enclave_metadata_ev_mask,
         enclave_metadata_bitmap,
         enclave_metadata_thread_count,
         enclave_metadata_load_eptbr,
         enclave_metadata_dram_region_count,
         enclave_metadata_last_load_addr,
         thread_metadata_valid,
         thread_metadata_eid,
         thread_metadata_entry_pc,
         thread_metadata_entry_stack,
         thread_metadata_fault_pc,
         thread_metadata_fault_stack,
         enclave_metadata_thread_count,
         tap_enclave_metadata_valid,
         tap_enclave_metadata_addr_map,
         tap_enclave_metadata_addr_valid,
         tap_enclave_metadata_addr_excl,
         tap_enclave_metadata_entrypoint,
         tap_enclave_metadata_pc,
         tap_enclave_metadata_regs,
         tap_enclave_metadata_paused,
         tap_enclave_metadata_cache_conflict,
         cache_valid_map, cache_tag_map,
         rip, untrusted_regs,
         untrusted_addr_map, untrusted_addr_valid,
         untrusted_pc;

requires cpu_ptbr == k2_ppn_t;
requires cpu_parbase == 0bv9 ++ 0bv3 ++ 0bv12;
requires cpu_parmask == 0bv9 ++ 0bv3 ++ 255bv12;
requires cpu_eparbase == cpu_parbase;
requires cpu_eparmask == cpu_parmask;
requires cpu_dmarbase == 0bv9 ++ 0bv3 ++ 256bv12;
requires cpu_dmarmask == 0bv9 ++ 0bv3 ++ 255bv12;
requires (forall eid: enclave_id_t :: enclave_metadata_is_initialized[eid] ==> enclave_metadata_valid[eid]);
requires (forall eid: enclave_id_t :: enclave_metadata_valid[eid] ==> assigned(eid));
requires (forall eid: enclave_id_t ::
      enclave_metadata_valid[eid] ==> (owner[dram_region_for(eid)] == metadata_enclave_id));
requires (forall r: region_t, e: enclave_id_t ::
      ((owner[r] == e) && assigned(e)) ==> enclave_metadata_valid[e]);
requires (forall r: region_t, e: enclave_id_t ::
      ((owner[r] == e) && assigned(e)) ==> (owner[dram_region_for(e)] == metadata_enclave_id));
requires (forall p: wap_addr_t :: (owner[dram_region_for_w(p)] == free_enclave_id) ==> (mem[p] == k0_word_t));
requires (forall eid: enclave_id_t :: enclave_metadata_valid[eid] ==> (owner[dram_region_for(eid)] == metadata_enclave_id));
requires (forall r: region_t, eid: enclave_id_t :: (enclave_metadata_valid[eid] && assigned(eid)) ==>
      (owner[r] == eid <==> AND_8(enclave_metadata_bitmap[eid], LSHIFT_8(1bv8, 0bv5 ++ r)) != 0bv8));
requires (forall eid1, eid2: enclave_id_t ::
                (eid1 != eid2  && assigned(eid1) && assigned(eid2) && enclave_metadata_valid[eid1] && enclave_metadata_valid[eid2]) ==>
                (disjoint_bitmaps(enclave_metadata_bitmap[eid1], enclave_metadata_bitmap[eid2])));
requires (forall eid: enclave_id_t ::
                (assigned(eid) && enclave_metadata_valid[eid]) ==> disjoint_bitmaps(enclave_metadata_bitmap[eid], os_bitmap));
requires (forall r: region_t, e: enclave_id_t :: (enclave_metadata_valid[e] && assigned(e)) ==>
        (owner[r] != e ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
requires (forall r: region_t, e: enclave_id_t :: enclave_metadata_valid[e] ==>
        (!assigned(owner[r]) ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
requires (forall r: region_t :: ((owner[r] == null_enclave_id) ==> read_bitmap(os_bitmap, r) == 1bv1));
requires (forall r: region_t :: ((owner[r] != null_enclave_id) ==> read_bitmap(os_bitmap, r) == 0bv1));
requires (forall r: region_t, e : enclave_id_t :: ((owner[r] == e && assigned(e)) ==>
      (read_bitmap(enclave_metadata_bitmap[e], r) == 1bv1)));
requires (forall r: region_t, e : enclave_id_t :: ((owner[r] != e && assigned(e) && enclave_metadata_valid[e]) ==>
      (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
requires os_bitmap == cpu_drbmap;
requires assigned(core_info_enclave_id) ==> (enclave_metadata_valid[core_info_enclave_id] && enclave_metadata_is_initialized[core_info_enclave_id]);
requires assigned(core_info_enclave_id) ==> enclave_metadata_bitmap[core_info_enclave_id] == cpu_edrbmap;
requires (forall e1: enclave_id_t, e2: enclave_id_t :: (enclave_metadata_is_initialized[e1] && enclave_metadata_is_initialized[e2] && e1 != e2) ==>
      (enclave_metadata_load_eptbr[e1] != enclave_metadata_load_eptbr[e2]));
requires (forall e: enclave_id_t, r: region_t :: (enclave_metadata_valid[e] && enclave_metadata_is_initialized[e]) ==>
      (dram_region_for(enclave_metadata_load_eptbr[e] ++ 0bv12) == r ==> owner[r] == e));

    //TAP's invariants next
requires (cpu_enclave_id == tap_null_enc_id) ==> ((cpu_addr_map == untrusted_addr_map) && (forall v : vaddr_t :: tap_addr_perm_eq(cpu_addr_valid[v], untrusted_addr_valid[v])));
requires (cpu_enclave_id != tap_null_enc_id) ==> ((cpu_addr_map == tap_enclave_metadata_addr_map[cpu_enclave_id]) && (forall v : vaddr_t :: tap_addr_perm_eq(cpu_addr_valid[v], tap_enclave_metadata_addr_valid[cpu_enclave_id][v])));
requires (forall pa : wap_addr_t, e : tap_enclave_id_t :: (e != tap_null_enc_id && !tap_enclave_metadata_valid[e]) ==> (cpu_owner_map[pa] != e));

    //current enclave_ids are related
requires cpu_enclave_id == enclave_id_bv2int(core_info_enclave_id);
requires (cpu_enclave_id == tap_null_enc_id) <==> (core_info_enclave_id == null_enclave_id);
requires ((cpu_enclave_id != tap_null_enc_id) ==> tap_enclave_metadata_valid[cpu_enclave_id]) &&
          (core_info_enclave_id != null_enclave_id ==> enclave_metadata_valid[core_info_enclave_id]);

    //memories are related
requires (forall pa: wap_addr_t :: cpu_mem[pa] == mem[pa]);

    //metadata_valid maps are related
requires (forall eid: enclave_id_t :: enclave_metadata_is_initialized[eid] ==> tap_enclave_metadata_valid[enclave_id_bv2int(eid)]);
requires (forall eid: enclave_id_t :: (enclave_metadata_is_initialized[eid] && enclave_metadata_valid[eid]) <==> tap_enclave_metadata_valid[enclave_id_bv2int(eid)]);

    //page tables are related
requires (forall va: vaddr_t ::
      (untrusted_addr_map[va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va))));
requires (forall va: vaddr_t, eid: enclave_id_t :: tap_enclave_metadata_valid[enclave_id_bv2int(eid)] ==>
      ((in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) ==>
       (tap_enclave_metadata_addr_map[enclave_id_bv2int(eid)][va] == paddr2wpaddr(ptbl_addr_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)] ++ vaddr2offset(va)))) &&
      (!in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) ==>
       (tap_enclave_metadata_addr_map[enclave_id_bv2int(eid)][va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va))))));
requires (forall va: vaddr_t ::
      (untrusted_addr_valid[va] == acl2addrperm(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])));
requires (forall va: vaddr_t, eid: enclave_id_t :: tap_enclave_metadata_valid[enclave_id_bv2int(eid)] ==>
      ((in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) ==>
       (tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va] ==  acl2addrperm(ptbl_acl_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)]))) &&
      (!in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) ==>
       (tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va] == acl2addrperm(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])))));

    //Sanctum's owner map is related to TAP's owner map
requires (forall pa: wap_addr_t :: assigned(owner[dram_region_for_w(pa)]) ==>
      (enclave_metadata_is_initialized[owner[dram_region_for_w(pa)]] ==> (enclave_id_bv2int(owner[dram_region_for_w(pa)]) == cpu_owner_map[pa])));
requires (forall pa: wap_addr_t :: (owner[dram_region_for_w(pa)] == null_enclave_id) <==> (tap_null_enc_id == cpu_owner_map[pa]));
requires (forall pa: wap_addr_t :: !assigned(owner[dram_region_for_w(pa)]) <==> (tap_null_enc_id == cpu_owner_map[pa]));

    //Sanctum's bitmaps are related to TAP's owner maps
requires (forall pa: wap_addr_t :: (read_bitmap(os_bitmap, dram_region_for_w(pa)) == 1bv1) <==> (cpu_owner_map[pa] == tap_null_enc_id));
requires (forall pa: wap_addr_t, e: enclave_id_t :: (enclave_metadata_valid[e] && assigned(e)) ==>
      ((read_bitmap(enclave_metadata_bitmap[e], dram_region_for_w(pa)) == 1bv1) <==> (cpu_owner_map[pa] == enclave_id_bv2int(e))));

ensures cpu_ptbr == k2_ppn_t;
ensures cpu_parbase == 0bv9 ++ 0bv3 ++ 0bv12;
ensures cpu_parmask == 0bv9 ++ 0bv3 ++ 255bv12;
ensures cpu_eparbase == cpu_parbase;
ensures cpu_eparmask == cpu_parmask;
ensures cpu_dmarbase == 0bv9 ++ 0bv3 ++ 256bv12;
ensures cpu_dmarmask == 0bv9 ++ 0bv3 ++ 255bv12;
ensures (forall eid: enclave_id_t :: enclave_metadata_is_initialized[eid] ==> enclave_metadata_valid[eid]);
ensures (forall eid: enclave_id_t :: enclave_metadata_valid[eid] ==> assigned(eid));
ensures (forall eid: enclave_id_t ::
      enclave_metadata_valid[eid] ==> (owner[dram_region_for(eid)] == metadata_enclave_id));
ensures (forall r: region_t, e: enclave_id_t ::
      ((owner[r] == e) && assigned(e)) ==> enclave_metadata_valid[e]);
ensures (forall r: region_t, e: enclave_id_t ::
      ((owner[r] == e) && assigned(e)) ==> (owner[dram_region_for(e)] == metadata_enclave_id));
ensures (forall eid: enclave_id_t :: enclave_metadata_valid[eid] ==> (owner[dram_region_for(eid)] == metadata_enclave_id));
ensures (forall p: wap_addr_t :: (owner[dram_region_for_w(p)] == free_enclave_id) ==> (mem[p] == k0_word_t));
ensures (forall r: region_t, eid: enclave_id_t :: (enclave_metadata_valid[eid] && assigned(eid)) ==>
      (owner[r] == eid <==> AND_8(enclave_metadata_bitmap[eid], LSHIFT_8(1bv8, 0bv5 ++ r)) != 0bv8));
ensures (forall eid1, eid2: enclave_id_t ::
                (eid1 != eid2  && assigned(eid1) && assigned(eid2) && enclave_metadata_valid[eid1] && enclave_metadata_valid[eid2]) ==>
                (disjoint_bitmaps(enclave_metadata_bitmap[eid1], enclave_metadata_bitmap[eid2])));
ensures (forall eid: enclave_id_t ::
                (assigned(eid) && enclave_metadata_valid[eid]) ==> disjoint_bitmaps(enclave_metadata_bitmap[eid], os_bitmap));
ensures (forall r: region_t, e: enclave_id_t :: (enclave_metadata_valid[e] && assigned(e)) ==>
        (owner[r] != e ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
ensures (forall r: region_t, e: enclave_id_t :: enclave_metadata_valid[e] ==>
        (!assigned(owner[r]) ==> (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
ensures (forall r: region_t :: ((owner[r] == null_enclave_id) ==> read_bitmap(os_bitmap, r) == 1bv1));
ensures (forall r: region_t :: ((owner[r] != null_enclave_id) ==> read_bitmap(os_bitmap, r) == 0bv1));
ensures (forall r: region_t, e : enclave_id_t :: ((owner[r] == e && assigned(e)) ==>
      (read_bitmap(enclave_metadata_bitmap[e], r) == 1bv1)));
ensures (forall r: region_t, e : enclave_id_t :: ((owner[r] != e && assigned(e) && enclave_metadata_valid[e]) ==>
      (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
ensures os_bitmap == cpu_drbmap;
ensures assigned(core_info_enclave_id) ==> (enclave_metadata_valid[core_info_enclave_id] && enclave_metadata_is_initialized[core_info_enclave_id]);
ensures assigned(core_info_enclave_id) ==> enclave_metadata_bitmap[core_info_enclave_id] == cpu_edrbmap;
ensures (forall e1: enclave_id_t, e2: enclave_id_t :: (enclave_metadata_is_initialized[e1] && enclave_metadata_is_initialized[e2] && e1 != e2) ==>
      (enclave_metadata_load_eptbr[e1] != enclave_metadata_load_eptbr[e2]));
ensures (forall e: enclave_id_t, r: region_t :: (enclave_metadata_valid[e] && enclave_metadata_is_initialized[e]) ==>
      (dram_region_for(enclave_metadata_load_eptbr[e] ++ 0bv12) == r ==> owner[r] == e));

    //TAP's invariants next
ensures (cpu_enclave_id == tap_null_enc_id) ==> ((cpu_addr_map == untrusted_addr_map) && (forall v : vaddr_t :: tap_addr_perm_eq(cpu_addr_valid[v], untrusted_addr_valid[v])));
ensures (cpu_enclave_id != tap_null_enc_id) ==> ((cpu_addr_map == tap_enclave_metadata_addr_map[cpu_enclave_id]) && (forall v : vaddr_t :: tap_addr_perm_eq(cpu_addr_valid[v], tap_enclave_metadata_addr_valid[cpu_enclave_id][v])));
ensures (forall pa : wap_addr_t, e : tap_enclave_id_t :: (e != tap_null_enc_id && !tap_enclave_metadata_valid[e]) ==> (cpu_owner_map[pa] != e));

    //current enclave_ids are related
ensures cpu_enclave_id == enclave_id_bv2int(core_info_enclave_id);
ensures (cpu_enclave_id == tap_null_enc_id) <==> (core_info_enclave_id == null_enclave_id);
ensures ((cpu_enclave_id != tap_null_enc_id) ==> tap_enclave_metadata_valid[cpu_enclave_id]) &&
          (core_info_enclave_id != null_enclave_id ==> enclave_metadata_valid[core_info_enclave_id]);

    //memories are related
ensures (forall pa: wap_addr_t :: cpu_mem[pa] == mem[pa]);

    //metadata_valid maps are related
ensures (forall eid: enclave_id_t :: (enclave_metadata_is_initialized[eid] && enclave_metadata_valid[eid]) <==> tap_enclave_metadata_valid[enclave_id_bv2int(eid)]);

    //page tables are related
ensures (forall va: vaddr_t ::
      (untrusted_addr_map[va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va))));
ensures (forall va: vaddr_t, eid: enclave_id_t :: tap_enclave_metadata_valid[enclave_id_bv2int(eid)] ==>
      ((in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) ==>
       (tap_enclave_metadata_addr_map[enclave_id_bv2int(eid)][va] == paddr2wpaddr(ptbl_addr_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)] ++ vaddr2offset(va)))) &&
      (!in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) ==>
       (tap_enclave_metadata_addr_map[enclave_id_bv2int(eid)][va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va))))));
ensures (forall va: vaddr_t ::
      (untrusted_addr_valid[va] == acl2addrperm(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])));
ensures (forall va: vaddr_t, eid: enclave_id_t :: tap_enclave_metadata_valid[enclave_id_bv2int(eid)] ==>
      ((in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) ==>
       (tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va] ==  acl2addrperm(ptbl_acl_map[enclave_metadata_load_eptbr[eid], vaddr2vpn(va)]))) &&
      (!in_enclave_mem(va, enclave_metadata_ev_base[eid], enclave_metadata_ev_mask[eid]) ==>
       (tap_enclave_metadata_addr_valid[enclave_id_bv2int(eid)][va] == acl2addrperm(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])))));

    //Sanctum's owner map is related to TAP's owner map
ensures (forall pa: wap_addr_t :: assigned(owner[dram_region_for_w(pa)]) ==>
      (enclave_metadata_is_initialized[owner[dram_region_for_w(pa)]] ==> (enclave_id_bv2int(owner[dram_region_for_w(pa)]) == cpu_owner_map[pa])));
ensures (forall pa: wap_addr_t :: (owner[dram_region_for_w(pa)] == null_enclave_id) ==> (tap_null_enc_id == cpu_owner_map[pa]));
ensures (forall pa: wap_addr_t :: (tap_null_enc_id == cpu_owner_map[pa]) ==> (owner[dram_region_for_w(pa)] == null_enclave_id));
ensures (forall pa: wap_addr_t :: !assigned(owner[dram_region_for_w(pa)]) <==> (tap_null_enc_id == cpu_owner_map[pa]));

    //Sanctum's bitmaps are related to TAP's owner maps
ensures (forall pa: wap_addr_t :: (read_bitmap(os_bitmap, dram_region_for_w(pa)) == 1bv1) <==> (cpu_owner_map[pa] == tap_null_enc_id));
ensures (forall pa: wap_addr_t, e: enclave_id_t :: (enclave_metadata_valid[e] && assigned(e)) ==>
      ((read_bitmap(enclave_metadata_bitmap[e], dram_region_for_w(pa)) == 1bv1) <==> (cpu_owner_map[pa] == enclave_id_bv2int(e))));
{
  if (*) {
    assume false; assume cpu_enclave_id == tap_null_enc_id;
    call refinement_proof_step_load();
  } else if (*) {
    assume false;
    call refinement_proof_step_store();
  } else if (*) {
    assume false;
    call refinement_proof_step_create_metadata_region();
  } else if (*) {
    assume false;
    call refinement_proof_step_create_enclave();
  } else if (*) {
    assume false;
    call refinement_proof_step_assign_dram_region();
  } else if (*) {
     assume false;
     call refinement_proof_step_free_dram_region();
  } else if (*) {
    assume false;
    call refinement_proof_step_load_thread();
  } else if (*) {
    assume false;
    call refinement_proof_step_launch();
  } else if (*) {
    assume false;
    call refinement_proof_step_enter_enclave();
  } else if (*) {
    assume false;
    call refinement_proof_step_exit_enclave();
  } else if (*) {
    assume false; // cpu_enclave_id == tap_null_enc_id;
    call refinement_proof_step_delete_enclave();
  }
}

procedure {:inline 1} refinement_proof_step_load()
modifies cache_valid_map, cache_tag_map, cpu_addr_valid;
{
  var vaddr: vaddr_t;
  var tap_data, sanctum_data: word_t;
  var sanctum_exn: bool;
  var tap_exn: exception_t;
  var cpu_mode: riscv_mode_t;
  var valid: bool;
  var paddr: paddr_t;
  var acl: pte_acl_t;
  var hit: bool;

  havoc vaddr;
  havoc cpu_mode; assume cpu_mode == cpu_mode_const; assume cpu_mode != RISCV_MODE_M;
  call valid, paddr, acl := translate(vaddr, riscv_access_read, cpu_mode, cpu_mode_pum_const, cpu_mode_mxr_const);
  call sanctum_data, sanctum_exn := RISCV_ISA_load(vaddr);
  assert valid <==> !sanctum_exn;
  if (!sanctum_exn) {
    assert read_bitmap(cpu_drbmap, dram_region_for(paddr)) == 1bv1 || read_bitmap(cpu_edrbmap, dram_region_for(paddr)) == 1bv1;
    assert owner[dram_region_for(paddr)] == null_enclave_id || owner[dram_region_for(paddr)] == core_info_enclave_id;
    call tap_data, tap_exn, hit := load_va(vaddr);
    assert (tap_exn == excp_none);
    assert (tap_data == sanctum_data);
  }
}

procedure {:inline 1} refinement_proof_step_store()
modifies cpu_mem, mem, cache_valid_map, cache_tag_map, cpu_addr_valid;
{
  var vaddr: vaddr_t;
  var tap_data, sanctum_data: word_t;
  var sanctum_exn: bool;
  var tap_exn: exception_t;
  var cpu_mode: riscv_mode_t;
  var valid: bool;
  var paddr: paddr_t;
  var acl: pte_acl_t;
  var hit: bool;

  havoc vaddr, sanctum_data;
  havoc cpu_mode; assume cpu_mode == cpu_mode_const; assume cpu_mode != RISCV_MODE_M;
  call valid, paddr, acl := translate(vaddr, riscv_access_write, cpu_mode, cpu_mode_pum_const, cpu_mode_mxr_const);
  call sanctum_exn := RISCV_ISA_store(vaddr, sanctum_data);
  assert valid <==> !sanctum_exn;
  if (!sanctum_exn) {
    assert read_bitmap(cpu_drbmap, dram_region_for(paddr)) == 1bv1 || read_bitmap(cpu_edrbmap, dram_region_for(paddr)) == 1bv1;
    assert owner[dram_region_for(paddr)] == null_enclave_id || owner[dram_region_for(paddr)] == core_info_enclave_id;
    call tap_exn, hit := store_va(vaddr, sanctum_data);
    assert (tap_exn == excp_none);
  }
}

procedure {:inline 1} refinement_proof_step_create_metadata_region()
modifies owner;
{
  var region: region_t;
  var api_result: api_result_t;

  havoc region;
  call api_result := create_metadata_region(region);
  if (api_result == monitor_ok) {
    assert true;
  }
}

procedure {:inline 1} refinement_proof_step_create_enclave()
modifies owner;
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
  var enclave_id: enclave_id_t, evbase: vaddr_t, evmask: vaddr_t;
  var api_result: api_result_t;
  havoc enclave_id, evbase, evmask;
  call api_result := create_enclave(enclave_id, evbase, evmask);
  if (api_result == monitor_ok) {
    assert true;
  }
}

procedure {:inline 1} refinement_proof_step_assign_dram_region()
modifies owner, os_bitmap, enclave_metadata_bitmap, cpu_drbmap;
{
  var region: region_t, enclave_id: enclave_id_t;
  var api_result: api_result_t;
  havoc region, enclave_id;
  call api_result := assign_dram_region(region, enclave_id);
  if (api_result == monitor_ok) {
    assert true;
  }
}

procedure {:inline 1} refinement_proof_step_free_dram_region()
modifies owner, os_bitmap, enclave_metadata_bitmap, cpu_drbmap;
{
  var region: region_t, enclave_id: enclave_id_t;
  var api_result: api_result_t;
  havoc region, enclave_id;
  //call api_result := free_dram_region(region, enclave_id);
  if (api_result == monitor_ok) {
    assert true;
  }
}

procedure {:inline 1} refinement_proof_step_load_thread()
modifies owner;
modifies thread_metadata_valid,
         thread_metadata_eid,
         thread_metadata_entry_pc,
         thread_metadata_entry_stack,
         thread_metadata_fault_pc,
         thread_metadata_fault_stack,
         enclave_metadata_thread_count;
{
  var thread_id: thread_id_t, enclave_id: enclave_id_t;
  var api_result: api_result_t;
  havoc enclave_id, thread_id;
  call api_result := load_thread(enclave_id,
                                 thread_id,
                                 enclave_metadata_ev_base[enclave_id], 0bv32, 0bv32, 0bv32);
  if (api_result == monitor_ok) {
    assert true;
  }
}

axiom (forall pa : wap_addr_t :: paddr2set(pa) == sanctum_paddr2set_w(pa));

procedure {:inline 1} refinement_proof_step_launch()
modifies enclave_metadata_is_initialized,
         cpu_owner_map,
         cpu_mem,
         tap_enclave_metadata_valid,
         tap_enclave_metadata_addr_map,
         tap_enclave_metadata_addr_valid,
         tap_enclave_metadata_addr_excl,
         tap_enclave_metadata_entrypoint,
         tap_enclave_metadata_pc,
         tap_enclave_metadata_regs,
         tap_enclave_metadata_paused,
         tap_enclave_metadata_cache_conflict;
{
  var api_result: api_result_t;
  var enclave_id: enclave_id_t;
  var addr_valid: addr_valid_t;
  var addr_map: addr_map_t;
  var excl_vaddr : excl_vaddr_t;
  var excl_map: excl_map_t;
  var entrypoint: vaddr_t;
  var status: enclave_op_result_t;

  havoc enclave_id;
  call api_result := init_enclave(enclave_id);
  if (api_result == monitor_ok) {
    //all phy addresses within owned dram_regions marked exclusive in excl_map
    havoc excl_map;
    assume (forall wa: wap_addr_t :: excl_map[wa] <==> owner[dram_region_for_w(wa)] == enclave_id);
    assert (forall p1, p2 : wap_addr_t :: (excl_map[p1] && !excl_map[p1]) ==> sanctum_paddr2set_w(p1) != sanctum_paddr2set_w(p2));
    assert (forall p1, p2 : wap_addr_t :: (excl_map[p1] && !excl_map[p1]) ==> paddr2set(p1) != paddr2set(p2));
    //all virtual addresses in ev_range are marked valid if enclave_metadata_load_eptbr's page tables says so
    havoc addr_valid;
    assume (forall va: vaddr_t :: (in_enclave_mem(va, enclave_metadata_ev_base[enclave_id], enclave_metadata_ev_mask[enclave_id]) ==>
                                   addr_valid[va] == acl2addrperm(ptbl_acl_map[enclave_metadata_load_eptbr[enclave_id], vaddr2vpn(va)])) &&
                                  (!in_enclave_mem(va, enclave_metadata_ev_base[enclave_id], enclave_metadata_ev_mask[enclave_id]) ==>
                                   addr_valid[va] == acl2addrperm(ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)])));
    //all virtual addresses in ev_range use enclave_metadata_load_eptbr's page tables address mapping
    havoc addr_map;
    assume (forall va: vaddr_t :: (in_enclave_mem(va, enclave_metadata_ev_base[enclave_id], enclave_metadata_ev_mask[enclave_id]) ==>
                                   addr_map[va] == paddr2wpaddr(ptbl_addr_map[enclave_metadata_load_eptbr[enclave_id], vaddr2vpn(va)] ++ vaddr2offset(va))) &&
                                  (!in_enclave_mem(va, enclave_metadata_ev_base[enclave_id], enclave_metadata_ev_mask[enclave_id]) ==>
                                   addr_map[va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va))));
    //we will have already populated the enclave region during copy_page, so no need to do anything during launch
    havoc entrypoint;
    havoc excl_vaddr;

    assume entrypoint == enclave_metadata_ev_base[enclave_id];
    // executable entrypoint.
    assume tap_addr_perm_x(addr_valid[entrypoint]);
    // exclusive entrypoint.
    assume excl_vaddr[entrypoint] && excl_map[addr_map[entrypoint]];
    assume (forall va : vaddr_t ::
      excl_vaddr[va] ==> in_enclave_mem(va, enclave_metadata_ev_base[enclave_id], enclave_metadata_ev_mask[enclave_id]));
    // FIXME: we have to prove these in the rest of the refinement.
    assume (forall v1, v2 : vaddr_t :: !vaddr_alias(excl_vaddr, addr_map, v1, v2)) &&
           (forall v : vaddr_t :: excl_vaddr[v] ==> excl_map[addr_map[v]]) && 
           (forall v : vaddr_t :: excl_vaddr[v] ==> tap_addr_perm_v(addr_valid[v]));
    assert enclave_id_bv2int(enclave_id) != tap_null_enc_id;
    assert !old(tap_enclave_metadata_valid[enclave_id_bv2int(enclave_id)]);
    call status := launch(enclave_id_bv2int(enclave_id), addr_valid, addr_map, excl_vaddr, excl_map, entrypoint);
    assert (forall p1, p2 : wap_addr_t :: (cpu_owner_map[p1] == enclave_id_bv2int(enclave_id) && cpu_owner_map[p1] != enclave_id_bv2int(enclave_id)) ==> paddr2set(p1) != paddr2set(p2));
    assert tap_enclave_metadata_cache_conflict[enclave_id_bv2int(enclave_id)];
    assert status == enclave_op_success;
  }
}

procedure {:inline 1} refinement_proof_step_enter_enclave()
modifies cpu_enclave_id,
         cpu_addr_map,
         cpu_addr_valid,
         cpu_pc,
         cpu_regs,
         core_info_enclave_id,
         core_info_thread_id,
         cpu_evbase, cpu_evmask,
         cpu_edrbmap, cpu_eptbr,
         rip, untrusted_regs,
         untrusted_addr_map, untrusted_addr_valid,
         untrusted_pc;
{
  var thread_id: thread_id_t, enclave_id: enclave_id_t;
  var api_result: api_result_t;
  var status: enclave_op_result_t;

  havoc enclave_id, thread_id;
  call api_result := enter_enclave(enclave_id, thread_id);
  if (api_result == monitor_ok) {
    call status := enter(enclave_id_bv2int(enclave_id));
    assert status == enclave_op_success;
  }
}

procedure {:inline 1} refinement_proof_step_exit_enclave()
modifies core_info_enclave_id, rip,
         cpu_regs,
         cpu_enclave_id,
         cpu_addr_valid,
         cpu_addr_map,
         cpu_pc,
         tap_enclave_metadata_addr_valid,
         tap_enclave_metadata_addr_map,
         tap_enclave_metadata_pc,
         tap_enclave_metadata_paused;
{
  var api_result: api_result_t;
  var status: enclave_op_result_t;

  call api_result := exit_enclave();
  if (api_result == monitor_ok) {
    call status := exit();
    assert status == enclave_op_success;
  }
}

procedure {:inline 1} refinement_proof_step_delete_enclave()
modifies enclave_metadata_valid, owner;
modifies cpu_mem, cpu_owner_map;
modifies tap_enclave_metadata_regs,
         tap_enclave_metadata_valid,
         tap_enclave_metadata_addr_map,
         tap_enclave_metadata_addr_valid,
         tap_enclave_metadata_pc;
modifies enclave_metadata_is_initialized;
{
  var enclave_id: enclave_id_t;
  var api_result: api_result_t;
  var status: enclave_op_result_t;

  havoc enclave_id;
  call api_result := delete_enclave(enclave_id);
  if (api_result == monitor_ok) {
    if (!old(enclave_metadata_is_initialized[enclave_id])) { return; }
    call status := destroy(enclave_id_bv2int(enclave_id));
    assert status == enclave_op_success;
  }
}

