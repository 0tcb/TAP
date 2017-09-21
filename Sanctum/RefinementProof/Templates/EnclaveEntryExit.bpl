procedure refinement_proof_step_enter_enclave();
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
    //__TEMPLATE_INSERT__ requires
    //dis__TEMPLATE_INSERT__ ensures


procedure refinement_proof_step_exit_enclave();
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
    //__TEMPLATE_INSERT__ requires
    //__TEMPLATE_INSERT__ ensures

