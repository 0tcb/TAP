implementation refinement_proof_step_create_metadata_region()
{
  var region: region_t;
  var api_result: api_result_t;
  var cpu_owner_map_old : owner_map_t;

  havoc region;
  call api_result := create_metadata_region(region);
  if (api_result == monitor_ok) {
    cpu_owner_map_old := cpu_owner_map;
    havoc cpu_owner_map;
    assume (forall pa : wap_addr_t ::
              if dram_region_for_w(pa) == region
                  then cpu_owner_map[pa] == tap_metadata_enc_id
                  else cpu_owner_map[pa] == cpu_owner_map_old[pa]);
  }
}

implementation refinement_proof_step_create_enclave()
{
  var enclave_id: enclave_id_t, evbase: vaddr_t, evmask: vaddr_t;
  var api_result: api_result_t;
  havoc enclave_id, evbase, evmask;
  call api_result := create_enclave(enclave_id, evbase, evmask);
  if (api_result == monitor_ok) {
    assert true;
  }
}

implementation refinement_proof_step_assign_dram_region()
{
  var region: region_t, enclave_id: enclave_id_t;
  var api_result: api_result_t;
  havoc region, enclave_id;
  call api_result := assign_dram_region(region, enclave_id);
  if (api_result == monitor_ok) {
    assert true;
  }
}

implementation refinement_proof_step_load_thread()
{
  var thread_id: thread_id_t, enclave_id: enclave_id_t;
  var api_result: api_result_t;
  var entry_pc: vaddr_t; 
  var entry_stack: vaddr_t; 
  var fault_pc: vaddr_t; 
  var fault_stack: vaddr_t;
  // var's are havoc'd by default.
  call api_result := load_thread(enclave_id, thread_id, enclave_metadata_ev_base[enclave_id], 0bv32, 0bv32, 0bv32);
  if (api_result == monitor_ok) {
    assert true;
  }
}

implementation refinement_proof_step_delete_thread()
{
  var thread_id: thread_id_t, enclave_id: enclave_id_t;
  var api_result: api_result_t;
  havoc enclave_id, thread_id;
  call api_result := delete_thread(thread_id);
  if (api_result == monitor_ok) {
    assert true;
  }
}

implementation refinement_proof_step_free_dram_region()
{
  var region: region_t;
  var api_result: api_result_t;
  var bmap : excl_map_t;
  var status: enclave_op_result_t;

  havoc bmap;
  assume (forall p : wap_addr_t :: bmap[p] <==> (dram_region_for_w(p) == region));
  call api_result := free_dram_region(region);
  if (api_result == monitor_ok) {
    assert (forall p : wap_addr_t :: bmap[p] ==> (cpu_owner_map[p] == tap_blocked_enc_id));
    call status := release_blocked_memory(bmap);
    assert (forall p : wap_addr_t :: 
              if bmap[p]
                 then (cpu_owner_map[p] == tap_null_enc_id && old(cpu_owner_map)[p] == tap_blocked_enc_id)
                 else (cpu_owner_map[p] == old(cpu_owner_map[p])));
    assert (status == enclave_op_success);
  }
}
