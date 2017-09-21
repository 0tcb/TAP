procedure refinement_proof_step_create_metadata_region();
    modifies owner, cpu_owner_map;
    //__TEMPLATE_INSERT__ requires
    //__TEMPLATE_INSERT__ ensures


procedure refinement_proof_step_create_enclave();
    modifies owner;
    modifies enclave_metadata_valid,
             enclave_metadata_is_initialized,
             enclave_metadata_ev_base,
             enclave_metadata_ev_mask,
             enclave_metadata_bitmap,
             enclave_metadata_thread_count,
             enclave_metadata_load_eptbr,
             enclave_metadata_dram_region_count,
             enclave_metadata_last_load_addr,
             enclave_metadata_measurement;
    //__TEMPLATE_INSERT__ requires
    //__TEMPLATE_INSERT__ ensures


procedure refinement_proof_step_assign_dram_region();
    modifies owner, os_bitmap, enclave_metadata_bitmap, cpu_drbmap;
    //__TEMPLATE_INSERT__ requires
    //__TEMPLATE_INSERT__ ensures


procedure refinement_proof_step_load_thread();
  modifies thread_metadata_valid,
           thread_metadata_eid,
           thread_metadata_entry_pc,
           thread_metadata_entry_stack,
           thread_metadata_fault_pc,
           thread_metadata_fault_stack,
           enclave_metadata_thread_count,
           enclave_metadata_measurement;
    //__TEMPLATE_INSERT__ requires
    //__TEMPLATE_INSERT__ ensures


procedure refinement_proof_step_delete_thread();
    modifies thread_metadata_valid, enclave_metadata_thread_count;
    //__TEMPLATE_INSERT__ requires
    //__TEMPLATE_INSERT__ ensures


procedure refinement_proof_step_free_dram_region();
    modifies owner, os_bitmap, mem, cpu_mem, cpu_owner_map;
    //__TEMPLATE_INSERT__ requires
    //__TEMPLATE_INSERT__ ensures

