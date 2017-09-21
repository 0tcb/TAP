/**********************************
 * Proof-related Helper Utils     *
 **********************************/
function {:inline} disjoint_bitmaps(b1: bv8, b2: bv8) : bool
  { AND_8(b1, b2) == 0bv8 }

const k_metadata_region_t : region_t;

procedure {:inline 1} adversarial_monitor_call()
  modifies owner,
           enclave_metadata_valid,
           enclave_metadata_is_initialized,
           enclave_metadata_ev_base,
           enclave_metadata_ev_mask,
           enclave_metadata_bitmap,
           enclave_metadata_load_eptbr,
           enclave_metadata_dram_region_count,
           enclave_metadata_last_load_addr,
           enclave_metadata_thread_count,
           enclave_metadata_measurement,
           thread_metadata_valid,
           thread_metadata_eid,
           thread_metadata_entry_pc,
           thread_metadata_entry_stack,
           thread_metadata_fault_pc,
           thread_metadata_fault_stack,
           ptbl_addr_map,
           ptbl_acl_map,
           cpu_ptbr,
           os_bitmap,
           cpu_drbmap,
           cpu_edrbmap,
           blocked_at,
           dram_regions_info_block_clock,
           core_flushed_at,
           mem;
{
  var region: region_t;
  var result: api_result_t;
  var eid: enclave_id_t;
  var tid: thread_id_t;
  var entry_pc: vaddr_t;
  var entry_stack: vaddr_t;
  var fault_pc: vaddr_t;
  var fault_stack: vaddr_t;
  var evbase: vaddr_t;
  var evmask: vaddr_t;
  var vaddr: vaddr_t;
  var paddr: paddr_t;
  var acl: pte_acl_t;
  var level: int;

  if (*) {
    havoc region;
    call result := create_metadata_region(region);
  } else if (*) {
    havoc eid, evbase, evmask;
    call result := create_enclave(eid, evbase, evmask);
  } else if (*) {
    havoc eid, vaddr, paddr, acl, level;
    call result := load_page_table(eid, vaddr, paddr, acl, level);
  } else if (*) {
    havoc region, eid;
    call result := assign_dram_region(region, eid);
  } else if (*) {
    havoc eid, tid, entry_pc, entry_stack, fault_pc, fault_stack;
    call result := load_thread(eid, tid, entry_pc, entry_stack, fault_pc, fault_stack);
  } else if (*) {
    havoc eid;
    call result := init_enclave(eid);
  } else if (*) {
    havoc region;
    call result := block_dram_region(region);
  } else if (*) {
    havoc region;
    call result := free_dram_region(region);
  } else if (*) {
    call result := flush_cached_dram_regions();
  } else if (*) {
    havoc tid;
    call result := delete_thread(tid);
  } else if (*) {
    havoc eid;
    call result := delete_enclave(eid);
  }
}

procedure {:inline 1} adversarial_os_computation()
  modifies mem, reg, ptbl_addr_map, ptbl_acl_map;
  modifies owner,
           enclave_metadata_valid,
           enclave_metadata_is_initialized,
           enclave_metadata_ev_base,
           enclave_metadata_ev_mask,
           enclave_metadata_bitmap,
           enclave_metadata_load_eptbr,
           enclave_metadata_dram_region_count,
           enclave_metadata_last_load_addr,
           enclave_metadata_thread_count,
           enclave_metadata_measurement,
           //ptbl_addr_map,
           //ptbl_acl_map,
           thread_metadata_valid,
           thread_metadata_eid,
           thread_metadata_entry_pc,
           thread_metadata_entry_stack,
           thread_metadata_fault_pc,
           thread_metadata_fault_stack,
           os_bitmap,
           cpu_drbmap,
           cpu_edrbmap,
           blocked_at,
           dram_regions_info_block_clock,
           core_flushed_at,
           cpu_ptbr;
{
  var vaddr: vaddr_t;
  var paddr: paddr_t;
  var acl: pte_acl_t;
  var exn: bool;
  var data: word_t;
  var success: bool;

  if (*) {
    havoc vaddr, data;
    call exn := RISCV_ISA_store(vaddr, data); //adversarial store
  } else if (*) {
    havoc vaddr;
    call data, exn := RISCV_ISA_load(vaddr); //adversarial load
  } else if (*) {
    //OS can muck around with its own page tables, which is not captured by store as we use an abstract MMU
    havoc vaddr, paddr, acl;
    call success := create_page_table_mapping(cpu_ptbr, vaddr, paddr, acl);
  } else if (*) {
    call adversarial_monitor_call();
  }
}

 procedure {:inline 1} adversarial_enclave_computation(eid: enclave_id_t, tid: thread_id_t)
  modifies mem, reg, ptbl_addr_map, ptbl_acl_map;
 {
   var vaddr: vaddr_t;
   var paddr: paddr_t;
   var acl: pte_acl_t;
   var exn: bool;
   var data: word_t;
   var success: bool;
   var seed: int;

   while(*)
     invariant (forall pa: wap_addr_t ::
       (owner[dram_region_for_w(pa)] != eid && owner[dram_region_for_w(pa)] != null_enclave_id) ==> mem[pa] == old(mem[pa]));
   {
     if (*) {
       havoc vaddr;
       call data, exn := RISCV_ISA_load(vaddr);
     } else if (*) {
       havoc vaddr, data;
       call exn := RISCV_ISA_store(vaddr, data);
     } else if (*) {
       havoc seed;
       call RISCV_ISA_misc(seed);
     } else if (*) {
       havoc vaddr, paddr, acl;
       //OS can muck around with its own page tables, which is not captured by store as we use an abstract MMU
       call success := create_page_table_mapping(cpu_eptbr, vaddr, paddr, acl);
     }
   }
}

procedure {:inline 1} initialize_page_tables(eid : enclave_id_t, tid: thread_id_t, enclave_dram_region: region_t)
  modifies ptbl_addr_map, ptbl_acl_map;
  modifies enclave_metadata_load_eptbr, cpu_ptbr;
  modifies enclave_metadata_measurement;
{
  var vaddr : vaddr_t;
  var paddr : paddr_t;
  var acl : pte_acl_t;
  var api_result : api_result_t;

  while (*)
    invariant (enclave_metadata_valid[eid]              &&
               thread_metadata_valid[tid]               &&
               thread_metadata_eid[tid] == eid);
    invariant (forall va: vaddr_t, pa: paddr_t ::
               does_translation_exist(ptbl_acl_map, enclave_metadata_load_eptbr[eid], va)   &&
               pa == translate_vaddr2paddr(ptbl_addr_map, enclave_metadata_load_eptbr[eid], va) ==>
                       owner[dram_region_for(pa)] == eid);
  {
      havoc vaddr;
      havoc paddr;
      havoc acl;

      if( acl2read(acl) && acl2valid(acl) && dram_region_for(paddr) == enclave_dram_region ) {
        call api_result := load_page_table(eid, vaddr, paddr, acl, 0);
        assume api_result == monitor_ok;
        assert enclave_metadata_valid[eid];
        assert thread_metadata_valid[tid];
        assert thread_metadata_eid[tid] == eid;
        assert (does_translation_exist(ptbl_acl_map, enclave_metadata_load_eptbr[eid], vaddr));
        assert (forall va: vaddr_t, pa: paddr_t ::
                  (does_translation_exist(ptbl_acl_map, enclave_metadata_load_eptbr[eid], va)   &&
                   pa == translate_vaddr2paddr(ptbl_addr_map, enclave_metadata_load_eptbr[eid], va)) ==>
                           owner[dram_region_for(pa)] == eid);
      }
  }
}

procedure {:inline 1} launch(used_page_map: used_page_map_t)
  returns (result_eid: enclave_id_t, result_tid: thread_id_t, used_page_map_new: used_page_map_t, enclave_dram_region: region_t)
  modifies enclave_metadata_valid,
           enclave_metadata_is_initialized,
           enclave_metadata_ev_base,
           enclave_metadata_ev_mask,
           enclave_metadata_bitmap,
           enclave_metadata_load_eptbr,
           enclave_metadata_dram_region_count,
           enclave_metadata_last_load_addr,
           enclave_metadata_thread_count,
           enclave_metadata_measurement,
           thread_metadata_valid,
           thread_metadata_eid,
           thread_metadata_entry_pc,
           thread_metadata_entry_stack,
           thread_metadata_fault_pc,
           thread_metadata_fault_stack,
           cpu_evbase,
           cpu_evmask,
           cpu_drbmap,
           cpu_edrbmap,
           cpu_eptbr,
           cpu_ptbr,
           cpu_parbase,
           cpu_eparbase,
           cpu_parmask,
           cpu_eparmask,
           cpu_dmarbase,
           cpu_dmarmask,
           owner,
           core_info_enclave_id,
           core_info_thread_id,
           os_bitmap;
  modifies ptbl_addr_map, ptbl_acl_map;
{
  var metadata_region : region_t;
  //var enclave_dram_region : region_t;
  var api_result : api_result_t;
  var eid : paddr_t;
  var tid : paddr_t;
  var ev_base : vaddr_t;
  var ev_mask : vaddr_t;
  var eid_arb, tid_arb : bv9;
  var owner_save: [region_t] enclave_id_t;
  var ptb: ppn_t;
  var pgavail: bool;
  var vaddr: vaddr_t;
  var paddr: paddr_t;
  var acl: pte_acl_t;
  var level: int;

  ev_base := kEV_BASE_vaddr_t; //0xFFFF0000
  ev_mask := kEV_MASK_vaddr_t; //0x0000FFFF
  metadata_region := k_metadata_region_t;
  havoc eid_arb, tid_arb;
  eid := eid_arb ++ metadata_region ++ 0bv12;
  tid := tid_arb ++ metadata_region ++ 0bv12;

  call api_result := create_metadata_region(metadata_region);
  assume api_result == monitor_ok;
  assert (owner[metadata_region] == metadata_enclave_id);
  assert (forall r: region_t :: r != metadata_region ==> owner[r] == old(owner[r]));

  call api_result := create_enclave(eid, ev_base, ev_mask);
  assume api_result == monitor_ok;
  assert (enclave_metadata_valid[eid] && !enclave_metadata_is_initialized[eid]);
  assert (forall e: enclave_id_t :: e != eid ==> (enclave_metadata_valid[e] == old(enclave_metadata_valid[e])));
  assert (forall e: enclave_id_t :: e != eid ==> (enclave_metadata_is_initialized[e] == old(enclave_metadata_is_initialized[e])));

  owner_save := owner;

  havoc enclave_dram_region;
  call api_result := assign_dram_region(enclave_dram_region, eid);
  assume api_result == monitor_ok;
  assert old(owner)[enclave_dram_region] == free_enclave_id;

  call api_result := load_thread(eid, tid, k0_vaddr_t, k0_vaddr_t, k0_vaddr_t, k0_vaddr_t);
  assume api_result == monitor_ok;

  // allocate a base page table
  call pgavail, ptb, used_page_map_new := alloc_page_from_region(used_page_map, enclave_dram_region);
  assume pgavail;
  assert dram_region_for(ppn2paddr(ptb)) == enclave_dram_region;
  call api_result := load_page_table(eid, vaddr, ppn2paddr(ptb), acl, 2);
  assume api_result == monitor_ok;
  assume (forall vpn: vpn_t :: acl2valid(ptbl_acl_map[enclave_metadata_load_eptbr[eid], vpn]) == false);
  assert (forall va: vaddr_t ::
      does_translation_exist(
        ptbl_acl_map,
        enclave_metadata_load_eptbr[eid],
        va) == false);
  // populate some virt->phys mappings
  call initialize_page_tables(eid, tid, enclave_dram_region);
  assert (owner[enclave_dram_region] == eid);
  assert (forall r: region_t :: (r != enclave_dram_region) ==> (owner[r] == owner_save[r]));
  assert (eid != null_enclave_id ==> os_bitmap == old(os_bitmap));
  assert (forall va: vaddr_t, pa: paddr_t ::
            (enclave_metadata_valid[eid]              &&
             thread_metadata_valid[tid]               &&
             thread_metadata_eid[tid] == eid          &&
             does_translation_exist(ptbl_acl_map, enclave_metadata_load_eptbr[eid], va)   &&
             pa == translate_vaddr2paddr(ptbl_addr_map, enclave_metadata_load_eptbr[eid], va)) ==>
                     owner[dram_region_for(pa)] == eid);

  call api_result := init_enclave(eid);
  assume api_result == monitor_ok;

  result_eid := eid;
  result_tid := tid;
  return;
}
/*
procedure DisjointBitmapsProof()
  modifies enclave_metadata_valid,
           enclave_metadata_is_initialized,
           enclave_metadata_ev_base,
           enclave_metadata_ev_mask,
           enclave_metadata_bitmap,
           enclave_metadata_load_eptbr,
           enclave_metadata_dram_region_count,
           enclave_metadata_last_load_addr,
           enclave_metadata_thread_count,
           thread_metadata_valid,
           thread_metadata_eid,
           thread_metadata_entry_pc,
           thread_metadata_entry_stack,
           thread_metadata_fault_pc,
           thread_metadata_fault_stack,
           cpu_evbase,
           cpu_evmask,
           cpu_drbmap,
           cpu_edrbmap,
           cpu_eptbr,
           cpu_ptbr,
           cpu_parbase,
           cpu_eparbase,
           cpu_parmask,
           cpu_eparmask,
           cpu_dmarbase,
           cpu_dmarmask,
           owner,
           core_info_enclave_id,
           core_info_thread_id,
           os_bitmap;
  modifies ptbl_addr_map, ptbl_acl_map;
{
  var launched_eid : enclave_id_t;
  var launched_tid : thread_id_t;
  var launched_dram_region : region_t;
  var used_page_map: used_page_map_t;
  call initialize_sanctum();
  while (*)
    invariant owner[0bv3] == null_enclave_id;
    invariant (forall r: region_t, e: enclave_id_t ::
      ((owner[r] == e) && assigned(e)) ==> enclave_metadata_valid[e]);
    invariant (forall r: region_t, e: enclave_id_t ::
      ((owner[r] == e) && assigned(e)) ==> (owner[dram_region_for(e)] == metadata_enclave_id));
    invariant (forall r: region_t, eid: enclave_id_t ::
                (enclave_metadata_valid[eid] && assigned(eid)) ==>
                (owner[r] == eid <==> AND_8(enclave_metadata_bitmap[eid], LSHIFT_8(1bv8, 0bv5 ++ r)) != 0bv8));
    invariant (forall eid1, eid2: enclave_id_t ::
                (eid1 != eid2  && assigned(eid1) && assigned(eid2) && enclave_metadata_valid[eid1] && enclave_metadata_valid[eid2]) ==>
                (disjoint_bitmaps(enclave_metadata_bitmap[eid1], enclave_metadata_bitmap[eid2])));
    invariant (forall eid: enclave_id_t ::
                (assigned(eid) && enclave_metadata_valid[eid]) ==> disjoint_bitmaps(enclave_metadata_bitmap[eid], os_bitmap));
    invariant (forall r: region_t :: (owner[r] != null_enclave_id) ==> (AND_8(os_bitmap, LSHIFT_8(1bv8, 0bv5 ++ r)) == 0bv8));
  {
    call launched_eid, launched_tid, used_page_map, launched_dram_region := launch(used_page_map);
  }
}
*/
procedure AdversaryIsolationProof()
  modifies enclave_metadata_valid,
           enclave_metadata_is_initialized,
           enclave_metadata_ev_base,
           enclave_metadata_ev_mask,
           enclave_metadata_bitmap,
           enclave_metadata_load_eptbr,
           enclave_metadata_dram_region_count,
           enclave_metadata_last_load_addr,
           enclave_metadata_thread_count,
           enclave_metadata_measurement,
           thread_metadata_valid,
           thread_metadata_eid,
           thread_metadata_entry_pc,
           thread_metadata_entry_stack,
           thread_metadata_fault_pc,
           thread_metadata_fault_stack,
           cpu_evbase,
           cpu_evmask,
           cpu_drbmap,
           cpu_edrbmap,
           cpu_eptbr,
           cpu_ptbr,
           cpu_parbase,
           cpu_eparbase,
           cpu_parmask,
           cpu_eparmask,
           cpu_dmarbase,
           cpu_dmarmask,
           cpu_edrbmap,
           blocked_at,
           core_flushed_at,
           dram_regions_info_block_clock,
           owner,
           core_info_enclave_id,
           core_info_thread_id,
           os_bitmap,
           mem,
           reg,
           rip;
  modifies ptbl_addr_map, ptbl_acl_map;
{
  var memp: mem_t;
  var launched_eid, dc_eid : enclave_id_t;
  var launched_tid, dc_tid : thread_id_t;
  var api_result : api_result_t;
  var used_page_map: used_page_map_t;
  var launched_dram_region, dc_dram_region : region_t;
  var exn : bool;
  var success : bool;
  var addr : vaddr_t;
  var phyaddr: paddr_t;
  var data : word_t;
  var acl : pte_acl_t;

  call initialize_sanctum();
  call launched_eid, launched_tid, used_page_map, launched_dram_region := launch(used_page_map);
  assert enclave_metadata_valid[launched_eid] && enclave_metadata_is_initialized[launched_eid];

  memp := mem;
  while (enclave_metadata_valid[launched_eid]) //until the attacker deletes us
    invariant core_info_enclave_id == null_enclave_id;
    //invariant owner[0bv3] == null_enclave_id;
    //invariant owner[k_metadata_region_t] == metadata_enclave_id;
    invariant enclave_metadata_valid[launched_eid] ==> enclave_metadata_is_initialized[launched_eid];
    invariant (forall eid: enclave_id_t ::
      (enclave_metadata_is_initialized[eid] && enclave_metadata_valid[eid]) ==> (assigned(eid)));
    invariant (forall eid: enclave_id_t ::
      enclave_metadata_valid[eid] ==> (owner[dram_region_for(eid)] == metadata_enclave_id));
    invariant (forall r: region_t, e: enclave_id_t ::
      ((owner[r] == e) && assigned(e)) ==> enclave_metadata_valid[e]);
    invariant (forall r: region_t, e: enclave_id_t ::
      ((owner[r] == e) && assigned(e)) ==> (owner[dram_region_for(e)] == metadata_enclave_id));
    invariant (forall eid1, eid2: enclave_id_t ::
                (eid1 != eid2  && assigned(eid1) && assigned(eid2) && enclave_metadata_valid[eid1] && enclave_metadata_valid[eid2]) ==>
                (disjoint_bitmaps(enclave_metadata_bitmap[eid1], enclave_metadata_bitmap[eid2])));
    invariant (forall eid: enclave_id_t ::
                (assigned(eid) && enclave_metadata_valid[eid]) ==> disjoint_bitmaps(enclave_metadata_bitmap[eid], os_bitmap));
    invariant (forall r: region_t, eid: enclave_id_t ::
      (enclave_metadata_valid[eid] && assigned(eid)) ==> (owner[r] == eid <==> AND_8(enclave_metadata_bitmap[eid], LSHIFT_8(1bv8, 0bv5 ++ r)) != 0bv8));
    invariant (forall r: region_t :: ((owner[r] == null_enclave_id) ==> read_bitmap(os_bitmap, r) == 1bv1));
    invariant (forall r: region_t :: ((owner[r] != null_enclave_id) ==> read_bitmap(os_bitmap, r) == 0bv1));
    invariant (forall r: region_t, e : enclave_id_t :: ((owner[r] == e && assigned(e)) ==>
      (read_bitmap(enclave_metadata_bitmap[e], r) == 1bv1)));
    invariant (forall r: region_t, e : enclave_id_t :: ((owner[r] != e && assigned(e) && enclave_metadata_valid[e]) ==>
      (read_bitmap(enclave_metadata_bitmap[e], r) == 0bv1)));
    invariant os_bitmap == cpu_drbmap;
    invariant assigned(core_info_enclave_id) ==> enclave_metadata_bitmap[core_info_enclave_id] == cpu_edrbmap;
    invariant (forall pa: paddr_t :: (owner[dram_region_for(pa)] == launched_eid) ==> (memp[paddr2wpaddr(pa)] == mem[paddr2wpaddr(pa)]));
    invariant (owner[launched_dram_region] == launched_eid);
  {
    if (*) {
      // launch an enclave.
      call dc_eid, dc_tid, used_page_map, dc_dram_region := launch(used_page_map);
      assert dc_dram_region != launched_dram_region;
    } else if (*) {
      // run some random enclave
      havoc dc_eid, dc_tid; assume dc_eid != launched_eid;
      call api_result := enter_enclave(dc_eid, dc_tid);
      if (api_result == monitor_ok) {
        call adversarial_enclave_computation(dc_eid, dc_tid);
        call api_result := exit_enclave();
      }
    } else if(*) {
      call adversarial_os_computation();
    }
  }
}
