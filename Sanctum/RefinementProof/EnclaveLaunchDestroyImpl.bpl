implementation refinement_proof_step_launch()
{
  var api_result: api_result_t;
  var enclave_id: enclave_id_t;
  var addr_valid: addr_valid_t;
  var addr_map: addr_map_t;
  var excl_vaddr : excl_vaddr_t;
  var excl_map: excl_map_t;
  var entrypoint: vaddr_t;
  var status: enclave_op_result_t;
  var eptbr: ppn_t;
  var tap_eid: tap_enclave_id_t;

  havoc enclave_id;
  call api_result := init_enclave(enclave_id);
  if (api_result == monitor_ok) {
    tap_eid := enclave_id_bv2int(enclave_id);
    eptbr := enclave_metadata_load_eptbr[enclave_id];

    // all phy addresses within owned dram_regions marked exclusive in excl_map
    havoc excl_map;
    assume (forall wa: wap_addr_t :: excl_map[wa] <==> owner[dram_region_for_w(wa)] == enclave_id);
    //all virtual addresses in ev_range are marked valid if enclave_metadata_load_eptbr's page tables says so
    havoc excl_vaddr;
    assume (forall va : vaddr_t ::
      excl_vaddr[va] == in_enclave_mem(va, enclave_metadata_ev_base[enclave_id], enclave_metadata_ev_mask[enclave_id]));
    havoc addr_valid;
    havoc addr_map;
    // inside evrange.
    // all virtual addresses in ev_range use enclave_metadata_load_eptbr's page tables
    assume (forall va: vaddr_t :: excl_vaddr[va] ==> 
              tap_sanctum_perm_eq(addr_valid[va], ptbl_acl_map[eptbr, vaddr2vpn(va)]));
    assume (forall va: vaddr_t :: excl_vaddr[va] ==> 
              (addr_map[va] == paddr2wpaddr(ptbl_addr_map[eptbr, vaddr2vpn(va)] ++ vaddr2offset(va))));
    // outside evrange.
    // all virtual addresses not in ev_range use the OS's page table 
    assume (forall va: vaddr_t :: !excl_vaddr[va] ==> 
              tap_sanctum_perm_eq(addr_valid[va], ptbl_acl_map[cpu_ptbr, vaddr2vpn(va)]));
    assume (forall va: vaddr_t :: !excl_vaddr[va] ==> 
              (addr_map[va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va))));
    // we will have already populated the enclave region during copy_page, so no need to do anything during launch
    havoc entrypoint;
    assume entrypoint == enclave_metadata_ev_base[enclave_id];
    // executable entrypoint.
    assume tap_addr_perm_x(addr_valid[entrypoint]);
    // exclusive entrypoint.
    assume excl_vaddr[entrypoint] && excl_map[addr_map[entrypoint]];
    // FIXME: we have to prove these in the rest of the refinement.
    assume (forall v1, v2 : vaddr_t :: !vaddr_alias(excl_vaddr, addr_map, v1, v2));
    assume (forall v : vaddr_t :: excl_vaddr[v] ==> excl_map[addr_map[v]]);
    assume (forall v : vaddr_t :: excl_vaddr[v] ==> tap_addr_perm_v(addr_valid[v]));
    call status := launch(tap_eid, addr_valid, addr_map, excl_vaddr, excl_map, entrypoint);
    assert (status == enclave_op_success);
  }
}

implementation refinement_proof_step_delete_enclave()
{
  var enclave_id: enclave_id_t;
  var tap_eid : tap_enclave_id_t;
  var api_result: api_result_t;
  var cpu_owner_map_p : owner_map_t;
  var enc_mem_map : excl_map_t;
  var status: enclave_op_result_t;
  var inited : bool;

  havoc enclave_id;
  havoc enc_mem_map;

  inited := enclave_metadata_is_initialized[enclave_id];
  assume (forall p : wap_addr_t :: 
            enc_mem_map[p] == (owner[dram_region_for_w(p)] == enclave_id));
  call api_result := delete_enclave(enclave_id);

  if (api_result == monitor_ok) {
    if (!inited) { 
      call status := block_memory_region(enc_mem_map);
    } else {
      call status := destroy(enclave_id_bv2int(enclave_id));
    }
    assert status == enclave_op_success;
  }
}
