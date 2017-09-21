procedure refinement_proof_step_launch();
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
    //__TEMPLATE_INSERT__ requires
    //__TEMPLATE_INSERT__ ensures


procedure refinement_proof_step_delete_enclave();
    modifies enclave_metadata_valid, owner;
    modifies cpu_mem, cpu_owner_map;
    modifies tap_enclave_metadata_regs,
             tap_enclave_metadata_valid,
             tap_enclave_metadata_pc;
    modifies enclave_metadata_is_initialized;
    //__TEMPLATE_INSERT__ requires
    //__TEMPLATE_INSERT__ ensures

