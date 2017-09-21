type observer_t;
const unique k_mem_observer_t : observer_t;
const unique k_cache_observer_t : observer_t;
const unique k_pt_observer_t : observer_t;

procedure {:inline 1} MemObserverComputation(
    /* next PC value.           */  r_pc : vaddr_t,
    /* registers to read/write. */  r_read : regindex_t, r_write : regindex_t, r_data: word_t,
    /* mem. to read/write.      */  l_vaddr: vaddr_t, s_vaddr: vaddr_t, s_data : word_t,
    /* "pt" entry to read       */  r_pt_eid : tap_enclave_id_t, r_pt_va : vaddr_t,
    /* "pt" entry to change.    */  pt_eid : tap_enclave_id_t, pt_vaddr: vaddr_t, 
    /* "pt" entry to change.    */  pt_valid: addr_perm_t, pt_paddr: wap_addr_t)
    returns (observation : word_t)
    requires valid_regindex(r_read);
    requires valid_regindex(r_write);
 
    modifies cpu_mem;
    modifies cpu_regs;
    modifies cpu_pc;
    modifies cache_valid_map, cache_tag_map;
    modifies untrusted_addr_valid;
    modifies cpu_addr_valid;
    modifies cpu_addr_map;
    modifies tap_enclave_metadata_addr_valid;
    modifies tap_enclave_metadata_addr_map;
    modifies untrusted_addr_map;
{
    var excp         : exception_t;
    var l_word       : word_t;
    var r_word       : word_t;
    var hit_1, hit_2 : bool;
    var valid        : addr_perm_t;
    var paddr        : wap_addr_t;
    var status       : enclave_op_result_t;
    var l_way, s_way : cache_way_index_t;

    assume valid_cache_way_index(l_way);
    assume valid_cache_way_index(s_way);

    cpu_pc := r_pc;
    cpu_regs[r_write] := r_data;
    // store
    call excp, hit_1 := store_va(s_vaddr, s_data, s_way);
    // load
    call l_word, excp, hit_2 := load_va(l_vaddr, l_way);
    r_word := cpu_regs[r_read];
    observation := uf_observation_mem(cpu_pc, l_word, r_word);

    if (pt_eid == tap_null_enc_id) {
        call set_addr_map(pt_vaddr, pt_paddr, pt_valid);
    } else {
        call status := set_enclave_addr_map(pt_eid, pt_vaddr, pt_valid, pt_paddr);
    }
}

procedure {:inline 1} CacheObserverComputation(
    /* next PC value.           */  r_pc : vaddr_t,
    /* registers to read/write. */  r_read : regindex_t, r_write : regindex_t, r_data: word_t,
    /* mem. to read/write.      */  l_vaddr: vaddr_t, s_vaddr: vaddr_t, s_data : word_t,
    /* "pt" entry to read       */  r_pt_eid : tap_enclave_id_t, r_pt_va : vaddr_t,
    /* "pt" entry to change.    */  pt_eid : tap_enclave_id_t, pt_vaddr: vaddr_t, 
    /* "pt" entry to change.    */  pt_valid: addr_perm_t, pt_paddr: wap_addr_t,
    /* ways to change.          */  l_way, s_way : cache_way_index_t)
    returns (observation : word_t)
    requires valid_regindex(r_read);
    requires valid_regindex(r_write);
    requires valid_cache_way_index(s_way);
    requires valid_cache_way_index(l_way);
 
    modifies cpu_mem;
    modifies cpu_regs;
    modifies cpu_pc;
    modifies cache_valid_map, cache_tag_map;
    modifies tap_enclave_metadata_addr_valid;
    modifies tap_enclave_metadata_addr_map;
    modifies untrusted_addr_valid;
    modifies cpu_addr_valid;
    modifies cpu_addr_map;
    modifies untrusted_addr_map;
{
    var excp         : exception_t;
    var l_word       : word_t;
    var r_word       : word_t;
    var hit_1, hit_2 : bool;
    var valid        : addr_perm_t;
    var paddr        : wap_addr_t;
    var status       : enclave_op_result_t;

    cpu_pc := r_pc;
    cpu_regs[r_write] := r_data;
    call excp, hit_1 := store_va(s_vaddr, s_data, s_way);
    call valid, paddr := get_enclave_addr_map(r_pt_eid, r_pt_va);
    call l_word, excp, hit_2 := load_va(l_vaddr, l_way);
    r_word := cpu_regs[r_read];
    observation := uf_observation_cache(hit_1, hit_2);

    if (pt_eid == tap_null_enc_id) {
        call set_addr_map(pt_vaddr, pt_paddr, pt_valid);
    } else {
        call status := set_enclave_addr_map(pt_eid, pt_vaddr, pt_valid, pt_paddr);
    }
}

procedure {:inline 1} PTObserverComputation(
    /* next PC value.           */  r_pc : vaddr_t,
    /* registers to read/write. */  r_read : regindex_t, r_write : regindex_t, r_data: word_t,
    /* mem. to read/write.      */  l_vaddr: vaddr_t, s_vaddr: vaddr_t, s_data : word_t,
    /* "pt" entry to read       */  r_pt_eid : tap_enclave_id_t, r_pt_va : vaddr_t,
    /* "pt" entry to change.    */  pt_eid : tap_enclave_id_t, pt_vaddr: vaddr_t, 
    /* "pt" entry to change.    */  pt_valid: addr_perm_t, pt_paddr: wap_addr_t)
    returns (observation : word_t)
    requires valid_regindex(r_read);
    requires valid_regindex(r_write);
 
    modifies cpu_mem;
    modifies cpu_regs;
    modifies cpu_pc;
    modifies cache_valid_map, cache_tag_map;
    modifies untrusted_addr_valid;
    modifies tap_enclave_metadata_addr_valid;
    modifies tap_enclave_metadata_addr_map;
    modifies cpu_addr_valid;
    modifies cpu_addr_map;
    modifies untrusted_addr_map;
{
    var excp         : exception_t;
    var l_word       : word_t;
    var r_word       : word_t;
    var hit_1, hit_2 : bool;
    var valid        : addr_perm_t;
    var paddr        : wap_addr_t;
    var status       : enclave_op_result_t;
    var l_way, s_way : cache_way_index_t;

    assume valid_cache_way_index(l_way);
    assume valid_cache_way_index(s_way);

    // make observation.
    call valid, paddr := get_enclave_addr_map(r_pt_eid, r_pt_va);
    observation := uf_observation_pt(valid, paddr);

    // change state.
    cpu_pc := r_pc;
    cpu_regs[r_write] := r_data;
    call excp, hit_1 := store_va(s_vaddr, s_data, s_way);
    if (pt_eid == tap_null_enc_id) {
        call set_addr_map(pt_vaddr, pt_paddr, pt_valid);
    } else {
        call status := set_enclave_addr_map(pt_eid, pt_vaddr, pt_valid, pt_paddr);
    }
}

procedure {:inline 1} ObserverStep(
    /* observer          */ observer          : observer_t,
    /* Current mode      */ mode              : mode_t,
    /* Secret Enclave    */ eid               : tap_enclave_id_t,
    /* Adversary Enclave */ r_eid             : tap_enclave_id_t,
    /* Operation.        */ op                : tap_proof_op_t,
    /* next PC value.    */ r_pc              : vaddr_t,
    /* reg to read.      */ r_read            : regindex_t,
    /* reg to write      */ r_write           : regindex_t,
    /* data to write     */ r_data            : word_t,
    /* mem. to read.     */ l_vaddr           : vaddr_t,
    /* mem to write      */ s_vaddr           : vaddr_t,
    /* data to write     */ s_data            : word_t,
    /* pt entry to read  */ r_pt_eid          : tap_enclave_id_t, 
    /* pt entry to read  */ r_pt_va           : vaddr_t,
    /* pt eid            */ pt_eid            : tap_enclave_id_t,
    /* pt vaddr          */ pt_vaddr          : vaddr_t,
    /* pt valid          */ pt_valid          : addr_perm_t,
    /* pt paddr          */ pt_paddr          : wap_addr_t,
    /* VA->PA valid      */ r_addr_valid      : addr_valid_t,
    /* VA->PA map        */ r_addr_map        : addr_map_t,
    /* VA->excl map      */ r_excl_vaddr      : excl_vaddr_t,
    /* Private Mem Map   */ r_excl_map        : excl_map_t,
    /* Container Valid   */ r_container_valid : container_valid_t,
    /* Container Data    */ r_container_data  : container_data_t,
    /* Entrypoint        */ r_entrypoint      : vaddr_t,
    /* blocked mem       */ r_bmap            : excl_map_t,
    /* ways to change.   */ l_way, s_way      : cache_way_index_t)

    returns (observation: word_t, next_mode : mode_t, enclave_dead : bool, status : enclave_op_result_t)
    // PC stays reasonable.
    // Don't mess up TAP invariants.
    requires valid_regindex(r_read);
    requires valid_regindex(r_write);
    requires (observer == k_mem_observer_t   || 
              observer == k_cache_observer_t ||
              observer == k_pt_observer_t);

    requires valid_cache_way_index(s_way);
    requires valid_cache_way_index(l_way);

    modifies cpu_mem;
    modifies cpu_regs;
    modifies cpu_pc;
    modifies cpu_enclave_id;
    modifies cpu_addr_valid;
    modifies cpu_addr_map;
    modifies cpu_owner_map;
    modifies cache_valid_map, cache_tag_map;
    modifies untrusted_addr_valid;
    modifies untrusted_addr_map;
    modifies untrusted_regs;
    modifies untrusted_pc;
    modifies tap_enclave_metadata_valid;
    modifies tap_enclave_metadata_addr_map;
    modifies tap_enclave_metadata_addr_valid;
    modifies tap_enclave_metadata_addr_excl;
    modifies tap_enclave_metadata_entrypoint;
    modifies tap_enclave_metadata_pc;
    modifies tap_enclave_metadata_regs;
    modifies tap_enclave_metadata_paused;
    modifies tap_enclave_metadata_cache_conflict;
{
    // "default" for the next mode.
    next_mode := mode;
    // "default" for whether we kill enclave eid.
    enclave_dead := false;

    // start with a dummy observation.
    observation := k0_word_t;
    status := enclave_op_success;
    if (op == tap_proof_op_compute) {
        if (observer == k_mem_observer_t) {
            call observation := MemObserverComputation(r_pc, r_read, r_write, r_data,
                                                       l_vaddr, s_vaddr, s_data,
                                                       r_pt_eid, r_pt_va,
                                                       pt_eid, pt_vaddr, pt_valid, pt_paddr);
        } else if (observer == k_cache_observer_t) {
            call observation := CacheObserverComputation(r_pc, r_read, r_write, r_data,
                                                         l_vaddr, s_vaddr, s_data,
                                                         r_pt_eid, r_pt_va,
                                                         pt_eid, pt_vaddr, pt_valid, pt_paddr,
                                                         l_way, s_way);
        } else {
            call observation := PTObserverComputation(r_pc, r_read, r_write, r_data,
                                                      l_vaddr, s_vaddr, s_data,
                                                      r_pt_eid, r_pt_va,
                                                      pt_eid, pt_vaddr, pt_valid, pt_paddr);
        }
    } else if (op == tap_proof_op_launch) {
        // can't put current pc inside the enclave.
        assume !r_excl_map[cpu_addr_map[cpu_pc]];
        call InitOSMem(r_container_valid, r_container_data);
        call status := launch(r_eid, r_addr_valid, r_addr_map, 
                              r_excl_vaddr, r_excl_map, r_entrypoint);
        assert (r_eid == eid) ==> (status != enclave_op_success);
    } else if (op == tap_proof_op_destroy) {
        call status := destroy(r_eid);
        // the enclave has been destroyed.
        if (r_eid == eid && status == enclave_op_success) {
            enclave_dead := true;
        }
    } else if (op == tap_proof_op_enter) {
        call status := enter(r_eid);
        assert (cpu_enclave_id == tap_null_enc_id && r_eid == eid) ==> 
                (status == enclave_op_success);
        // switch to enclave mode.
        if (r_eid == eid && status == enclave_op_success) {
            next_mode := mode_enclave;
        }
    } else if (op == tap_proof_op_exit) {
        call status := exit();
    } else if (op == tap_proof_op_resume) {
        call status := resume(r_eid);
        // switch to enclave mode.
        assert (cpu_enclave_id == tap_null_enc_id && r_eid == eid && tap_enclave_metadata_paused[eid]) ==> 
                (status == enclave_op_success);
        if (r_eid == eid && status == enclave_op_success) {
            next_mode := mode_enclave;
        }
    } else if (op == tap_proof_op_pause) {
        call status := pause();
    } else if (op == tap_proof_op_release) {
        call status := release_blocked_memory(r_bmap);
    } else if (op == tap_proof_op_block) {
        call status := block_memory_region(r_bmap);
    }
}

procedure {:inline 1} EnclaveStep(
    /* Current mode */      mode              : mode_t,
    /* Secret Enclave */    eid               : tap_enclave_id_t,
    /* Operation. */        op                : tap_proof_op_t)

    returns (
        /* mode     */  next_mode : mode_t, 
        /* read     */  load_addr : vaddr_t, l_way : cache_way_index_t,
        /* store    */  store_addr : vaddr_t, store_data : word_t, s_way : cache_way_index_t
    )
    
    modifies cpu_mem;
    modifies cpu_regs;
    modifies cpu_pc;
    modifies cpu_enclave_id;
    modifies cpu_addr_valid;
    modifies cpu_addr_map;
    modifies cpu_owner_map;
    modifies cache_valid_map, cache_tag_map;
    modifies tap_enclave_metadata_valid;
    modifies tap_enclave_metadata_addr_map;
    modifies tap_enclave_metadata_addr_valid;
    modifies tap_enclave_metadata_addr_excl;
    modifies tap_enclave_metadata_pc;
    modifies tap_enclave_metadata_regs;
    modifies tap_enclave_metadata_paused;
    modifies tap_enclave_metadata_cache_conflict;
{
    var vaddr  : vaddr_t;
    var word   : word_t;
    var excp   : exception_t;
    var status : enclave_op_result_t;
    var hit    : bool;
    var owner  : tap_enclave_id_t;
    var way    : cache_way_index_t;

    if (op == tap_proof_op_compute) {
        // do whatever.
        havoc cpu_regs;
        havoc cpu_pc;

        // fetch from whereever inside the enclave.
        assume tap_enclave_metadata_addr_excl[eid][cpu_pc];
        assume tap_addr_perm_x(cpu_addr_valid[cpu_pc]);
        assert cpu_owner_map[cpu_addr_map[cpu_pc]] == eid;
        havoc way; assume valid_cache_way_index(way);
        call word, excp, hit := fetch_va(cpu_pc, way);
        assert (excp == excp_none);

        // load from whereever inside the enclave.
        havoc load_addr;
        assume tap_addr_perm_r(cpu_addr_valid[load_addr]);
        owner := cpu_owner_map[cpu_addr_map[load_addr]];
        assume owner == eid || owner == tap_null_enc_id;
        havoc l_way; assume valid_cache_way_index(l_way);
        call word, excp, hit := load_va(load_addr, l_way);
        assert (excp == excp_none);

        // store whatever inside the enclave.
        havoc store_addr, store_data;
        assume tap_addr_perm_w(cpu_addr_valid[store_addr]);
        owner := cpu_owner_map[cpu_addr_map[store_addr]];
        assume owner == eid || owner == tap_null_enc_id;
        havoc s_way; assume valid_cache_way_index(s_way);
        call excp, hit := store_va(store_addr, store_data, s_way);
        assert excp == excp_none;
        store_data := store_data;

        // stay in the same mode.
        next_mode := mode;
    } else if (op == tap_proof_op_exit) {
        call status := exit();
        assert status == enclave_op_success;
        // switch back to the observer. 
        next_mode := mode_untrusted;
    } else if (op == tap_proof_op_pause) {
        call status := exit();
        assert status == enclave_op_success;
        // switch back to the observer. 
        next_mode := mode_untrusted;
    }
}
