procedure refinement_proof_step_load();
    modifies cache_valid_map, 
             cache_tag_map, 
             cpu_addr_valid;
    //__TEMPLATE_INSERT__ requires
    //__TEMPLATE_INSERT__ ensures

procedure refinement_proof_step_store();
  modifies cache_valid_map,
           cache_tag_map,
           cpu_mem, mem,
           cpu_addr_valid;
  //__TEMPLATE_INSERT__ requires
  //__TEMPLATE_INSERT__ ensures
