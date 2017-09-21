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
  //__TEMPLATE_INSERT__ assume
  while (*)
    //__TEMPLATE_INSERT__ invariant
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
