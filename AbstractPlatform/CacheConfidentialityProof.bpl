procedure ProveConfidentialityCache(
    /* cache    */  cache_conflict : bool,
    /* page tbl */  obs_pt_ev_read : bool
)
    requires (!cpu_cache_enabled ==> !cache_conflict);

    modifies cpu_mem;
    modifies cpu_regs;
    modifies cpu_pc;
    modifies cpu_enclave_id;
    modifies cpu_addr_valid;
    modifies cpu_addr_map;
    modifies cpu_owner_map;
    modifies cache_valid_map, cache_tag_map;
    modifies cache_valid_map_1, cache_tag_map_1;
    modifies cache_valid_map_2, cache_tag_map_2;
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
    modifies cpu_mem_1;
    modifies cpu_regs_1;
    modifies cpu_pc_1;
    modifies cpu_enclave_id_1;
    modifies cpu_addr_valid_1;
    modifies cpu_addr_map_1;
    modifies cpu_owner_map_1;
    modifies untrusted_addr_valid_1;
    modifies untrusted_addr_map_1;
    modifies untrusted_regs_1;
    modifies untrusted_pc_1;
    modifies tap_enclave_metadata_valid_1;
    modifies tap_enclave_metadata_addr_map_1;
    modifies tap_enclave_metadata_addr_valid_1;
    modifies tap_enclave_metadata_addr_excl_1;
    modifies tap_enclave_metadata_entrypoint_1;
    modifies tap_enclave_metadata_pc_1;
    modifies tap_enclave_metadata_regs_1;
    modifies tap_enclave_metadata_paused_1;
    modifies tap_enclave_metadata_cache_conflict_1;
    modifies cpu_mem_2;
    modifies cpu_regs_2;
    modifies cpu_pc_2;
    modifies cpu_enclave_id_2;
    modifies cpu_addr_valid_2;
    modifies cpu_addr_map_2;
    modifies cpu_owner_map_2;
    modifies untrusted_addr_valid_2;
    modifies untrusted_addr_map_2;
    modifies untrusted_regs_2;
    modifies untrusted_pc_2;
    modifies tap_enclave_metadata_valid_2;
    modifies tap_enclave_metadata_addr_map_2;
    modifies tap_enclave_metadata_addr_valid_2;
    modifies tap_enclave_metadata_addr_excl_2;
    modifies tap_enclave_metadata_entrypoint_2;
    modifies tap_enclave_metadata_pc_2;
    modifies tap_enclave_metadata_regs_2;
    modifies tap_enclave_metadata_paused_2;
    modifies tap_enclave_metadata_cache_conflict_2;
{
    var eid, r_eid                                   : tap_enclave_id_t;
    var status, status_1, status_2                   : enclave_op_result_t;
    var e_addr_valid_1, e_addr_valid_2               : addr_valid_t;
    var e_addr_map_1, e_addr_map_2                   : addr_map_t;
    var e_excl_vaddr_1, e_excl_vaddr_2               : excl_vaddr_t;
    var e_excl_map                                   : excl_map_t;
    var e_container_data_1, e_container_data_2       : container_data_t;
    var e_entrypoint_1, e_entrypoint_2               : vaddr_t;
    var current_mode, current_mode_1, current_mode_2 : mode_t;
    var enclave_dead, enclave_dead_1, enclave_dead_2 : bool;
    var observation_1, observation_2                 : word_t;
    var e_proof_op, r_proof_op                       : tap_proof_op_t;
    var word_1, word_2                               : word_t;
    var paddr_1, paddr_2                             : wap_addr_t;
    var load_addr_1, load_addr_2                     : vaddr_t;
    var store_addr_1, store_addr_2                   : vaddr_t;
    var store_data_1, store_data_2                   : word_t;
    var r_addr_valid                                 : addr_valid_t;
    var r_addr_map                                   : addr_map_t;
    var r_excl_vaddr                                 : excl_vaddr_t;
    var r_excl_map                                   : excl_map_t;
    var r_bmap                                       : excl_map_t;
    var r_container_valid                            : container_valid_t;
    var r_container_data                             : container_data_t;
    var r_entrypoint                                 : vaddr_t;
    var r_pc                                         : vaddr_t;
    var r_read                                       : regindex_t;
    var r_write                                      : regindex_t;
    var r_data                                       : word_t;
    var r_pt_eid                                     : tap_enclave_id_t;
    var r_pt_va                                      : vaddr_t;
    var r_l_way, r_s_way                             : cache_way_index_t;
    var pt_eid                                       : tap_enclave_id_t;
    var pt_vaddr                                     : vaddr_t;
    var pt_valid                                     : addr_perm_t;
    var pt_paddr                                     : wap_addr_t;
    var l_vaddr                                      : vaddr_t;
    var s_vaddr                                      : vaddr_t;
    var s_data                                       : word_t;
    var l_way_1, s_way_1                             : cache_way_index_t;
    var l_way_2, s_way_2                             : cache_way_index_t;

    // initial state.
    call current_mode := InitialHavoc();
    assert tap_addr_perm_x(cpu_addr_valid[cpu_pc]);
    assert cpu_owner_map[cpu_addr_map[cpu_pc]] == cpu_enclave_id;
    assert cpu_enclave_id == tap_null_enc_id;
    // initialize the untrusted (OS) state with sane values.
    untrusted_addr_valid := cpu_addr_valid;
    untrusted_addr_map := cpu_addr_map;
    untrusted_pc := cpu_pc;

    // create two copies of state.
    call SaveContext_1();
    call SaveContext_2();

    // launch should not leave the PC in an untenable sitation.
    assume !e_excl_map[cpu_addr_map[cpu_pc]];
    // now launch enclave_1.
    call RestoreContext_1();
    call InitOSMem(e_excl_map, e_container_data_1);
    call status := launch(eid, e_addr_valid_1, e_addr_map_1,
                          e_excl_vaddr_1, e_excl_map, e_entrypoint_1);
    assume tap_enclave_metadata_cache_conflict[eid] == cache_conflict;
    assume status == enclave_op_success;
    call SaveContext_1();
    // and then enclave_2
    call RestoreContext_2();
    call InitOSMem(e_excl_map, e_container_data_2);
    call status := launch(eid, e_addr_valid_2, e_addr_map_2,
                          e_excl_vaddr_2, e_excl_map, e_entrypoint_2);
    assume status == enclave_op_success;
    assume tap_enclave_metadata_cache_conflict[eid] == cache_conflict;
    call SaveContext_2();

    // initial value of the observations.
    observation_1 := k0_word_t;
    observation_2 := k0_word_t;

    current_mode := mode_untrusted;
    while (!enclave_dead)
        //// The property ////
        invariant (!cache_conflict) ==> (observation_1 == observation_2);
        //// Cache ////
        // state that trusted cache lines do not conflict with untrusted lines.
        invariant (cpu_cache_enabled && !cache_conflict) ==>
                    (forall p1, p2 : wap_addr_t ::
                      (e_excl_map[p1] && !e_excl_map[p2]) ==>
                          (paddr2set(p1) != paddr2set(p2)));
        invariant (!enclave_dead && cpu_cache_enabled && !cache_conflict) ==>
                    (forall p : wap_addr_t, w : cache_way_index_t ::
                      (!e_excl_map[p] && valid_cache_way_index(w)) ==>
                        ((cache_valid_map_1[paddr2set(p), w] == cache_valid_map_2[paddr2set(p), w]) &&
                         (cache_valid_map_1[paddr2set(p), w] && cache_valid_map_2[paddr2set(p), w] ==>
                          (cache_tag_map_1[paddr2set(p), w] == cache_tag_map_2[paddr2set(p), w]))));
        //// General invariants /////
        invariant current_mode == mode_untrusted || current_mode == mode_enclave;
        // memory is not assigned to an enclave that doesn't exist.
        invariant (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                    (valid_enclave_id(e) && !tap_enclave_metadata_valid_1[e]) ==>
                        (cpu_owner_map_1[pa] != e));
        invariant (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                    (valid_enclave_id(e) && !tap_enclave_metadata_valid_2[e]) ==>
                        (cpu_owner_map_2[pa] != e));
        //-------------------------------------------------------------------//
        // CPU mode and CPU enclave ID must be consistent.
        //-------------------------------------------------------------------//
        invariant (forall e : tap_enclave_id_t :: 
                    !valid_enclave_id(e) ==> !tap_enclave_metadata_valid_1[tap_null_enc_id]);
        invariant (forall e : tap_enclave_id_t ::
                    !valid_enclave_id(e) ==> !tap_enclave_metadata_valid_2[tap_null_enc_id]);
        invariant (current_mode == mode_untrusted) ==> cpu_enclave_id_1 != eid;
        invariant (current_mode == mode_untrusted) ==> cpu_enclave_id_2 != eid;
        invariant (current_mode == mode_enclave) ==> (cpu_enclave_id_1 == eid);
        invariant (current_mode == mode_enclave) ==> (cpu_enclave_id_2 == eid);
        //-------------------------------------------------------------------//
        // Enclave 'eid' is mostly alive                                     //
        //-------------------------------------------------------------------//
        invariant (cpu_enclave_id_1 != tap_blocked_enc_id);
        invariant (cpu_enclave_id_2 != tap_blocked_enc_id);
        invariant (valid_enclave_id(eid));
        invariant (!enclave_dead ==> tap_enclave_metadata_valid_1[eid]);
        invariant (!enclave_dead ==> tap_enclave_metadata_valid_2[eid]);
        // maintain invariants about excl_vaddr.
        invariant (!enclave_dead) ==>
                        (tap_enclave_metadata_addr_excl_1[eid] == e_excl_vaddr_1);
        invariant (!enclave_dead) ==>
                        (tap_enclave_metadata_addr_excl_2[eid] == e_excl_vaddr_2);
        // invariants about addr_map
        invariant (forall v : vaddr_t ::
                      (!enclave_dead && e_excl_vaddr_1[v]) ==>
                          (tap_enclave_metadata_addr_map_1[eid][v] == e_addr_map_1[v]));
        invariant (forall v : vaddr_t ::
                      (!enclave_dead && e_excl_vaddr_2[v]) ==>
                          (tap_enclave_metadata_addr_map_2[eid][v] == e_addr_map_2[v]));
        // invariants about e_excl_addr
        invariant (forall p : wap_addr_t ::
                    (!enclave_dead) ==> ((cpu_owner_map_1[p] == eid) <==> e_excl_map[p]));
        invariant (forall p : wap_addr_t ::
                    (!enclave_dead) ==> ((cpu_owner_map_2[p] == eid) <==> e_excl_map[p]));
        invariant (forall v : vaddr_t, p : wap_addr_t ::
                        (!enclave_dead && e_excl_vaddr_1[v] && p == e_addr_map_1[v])
                            ==> e_excl_map[p]);
        invariant (forall v : vaddr_t, p : wap_addr_t ::
                        (!enclave_dead && e_excl_vaddr_2[v] && p == e_addr_map_2[v])
                            ==> e_excl_map[p]);
        //-------------------------------------------------------------------//
        // Now deal with the enclaves.
        //-------------------------------------------------------------------//
        invariant (forall v : vaddr_t ::
                    (current_mode == mode_enclave && e_excl_vaddr_1[v]) ==>
                        (cpu_addr_map_1[v] == e_addr_map_1[v]));
        invariant (forall v : vaddr_t ::
                    (current_mode == mode_enclave && e_excl_vaddr_2[v]) ==>
                        (cpu_addr_map_2[v] == e_addr_map_2[v]));
        //-------------------------------------------------------------------//
        // CPU state is the same                                             //
        //-------------------------------------------------------------------//
        // same PC.
        invariant (current_mode == mode_untrusted) ==> (cpu_pc_1 == cpu_pc_2);
        // same mode of operation.
        invariant (cpu_enclave_id_1 == cpu_enclave_id_2);
        // same regs.
        invariant (current_mode == mode_untrusted) ==> (cpu_regs_1 == cpu_regs_2);
        // same va->pa.
        invariant (current_mode == mode_untrusted) ==>
                    (cpu_addr_valid_1 == cpu_addr_valid_2);
        invariant (current_mode == mode_untrusted) ==>
                        (cpu_addr_map_1 == cpu_addr_map_2);
        // owner map is the same.
        invariant (forall pa : wap_addr_t :: (cpu_owner_map_1[pa] == cpu_owner_map_2[pa]));
        // memory is the same except for the enclave memory.
        invariant (forall pa : wap_addr_t :: !e_excl_map[pa] ==> (cpu_mem_1[pa] == cpu_mem_2[pa]));
        //-------------------------------------------------------------------//
        //// OS state is the same ////
        //-------------------------------------------------------------------//
        // OS va->pa
        invariant (untrusted_addr_valid_1 == untrusted_addr_valid_2);
        invariant (untrusted_addr_map_1 == untrusted_addr_map_2);
        // OS regs.
        invariant (untrusted_regs_1 == untrusted_regs_2);
        invariant (untrusted_pc_1 == untrusted_pc_2);
        //-------------------------------------------------------------------//
        // Enclave state is the same except for eid (mostly). Some it is the //
        // the same for eid as well (addr_map and addr_excl).                //
        //-------------------------------------------------------------------//
        // valid is the same except for eid.
        invariant (forall e : tap_enclave_id_t :: (e != eid) ==>
                    (tap_enclave_metadata_valid_1[e] == tap_enclave_metadata_valid_2[e]));
        // addr valid is the same except for eid.
        invariant (forall e : tap_enclave_id_t ::
                    (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_valid_2[e] && e != eid) ==>
                        (tap_enclave_metadata_addr_valid_1[e] == tap_enclave_metadata_addr_valid_2[e]));
        // the addr_map is the same for all enclaves.
        invariant (forall e : tap_enclave_id_t ::
                    (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_valid_2[e] && e != eid) ==>
                        (tap_enclave_metadata_addr_map_1[e] == tap_enclave_metadata_addr_map_2[e]));
        // addr_excl is the same except for eid.
        invariant (forall e : tap_enclave_id_t ::
                    (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_valid_2[e] && e != eid) ==>
                        (tap_enclave_metadata_addr_excl_1[e] == tap_enclave_metadata_addr_excl_2[e]));
        // entrypoints are the same except for eid.
        invariant (forall e : tap_enclave_id_t ::
                    (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_valid_2[e] && e != eid) ==>
                        (tap_enclave_metadata_entrypoint_1[e] == tap_enclave_metadata_entrypoint_2[e]));
        // pc is the same except for the eid
        invariant (forall e : tap_enclave_id_t ::
                    (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_valid_2[e] && e != eid) ==>
                        (tap_enclave_metadata_pc_1[e] == tap_enclave_metadata_pc_2[e]));
        // regs are the same except for the eid
        invariant (forall e : tap_enclave_id_t ::
                    (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_valid_2[e] && e != eid) ==>
                        (tap_enclave_metadata_regs_1[e] == tap_enclave_metadata_regs_2[e]));
        // paused is the same except for the eid
        invariant (forall e : tap_enclave_id_t ::
                    (tap_enclave_metadata_valid_1[e] && tap_enclave_metadata_valid_2[e]) ==>
                        (tap_enclave_metadata_paused_1[e] == tap_enclave_metadata_paused_2[e]));
    {
        if (current_mode == mode_untrusted) {
            havoc r_proof_op, r_eid, r_pc, r_read, r_write, r_data,
                  l_vaddr, s_vaddr, s_data, r_pt_eid, r_pt_va,
                  pt_eid, pt_vaddr, pt_valid, pt_paddr, r_addr_valid,
                  r_addr_map, r_excl_vaddr, r_excl_map, r_bmap,
                  r_container_valid, r_container_data, r_entrypoint, r_l_way, r_s_way;

            assume valid_regindex(r_read);
            assume valid_regindex(r_write);
            assume valid_cache_way_index(r_l_way);
            assume valid_cache_way_index(r_s_way);
            // trace_1
            call RestoreContext_1();
            call observation_1, current_mode_1, enclave_dead_1, status_1 :=
                                    ObserverStep(k_cache_observer_t, current_mode, eid, r_eid, r_proof_op,
                                                r_pc, r_read, r_write, r_data,
                                                l_vaddr, s_vaddr, s_data,
                                                r_pt_eid, r_pt_va,
                                                pt_eid, pt_vaddr, pt_valid, pt_paddr,
                                                r_addr_valid, r_addr_map, r_excl_vaddr,
                                                r_excl_map, r_container_valid, r_container_data,
                                                r_entrypoint, r_bmap,
                                                r_l_way, r_s_way);
            call SaveContext_1();

            // trace_2
            call RestoreContext_2();
            call observation_2, current_mode_2, enclave_dead_2, status_2 :=
                                    ObserverStep(k_cache_observer_t, current_mode, eid, r_eid, r_proof_op,
                                                r_pc, r_read, r_write, r_data,
                                                l_vaddr, s_vaddr, s_data,
                                                r_pt_eid, r_pt_va,
                                                pt_eid, pt_vaddr, pt_valid, pt_paddr,
                                                r_addr_valid, r_addr_map, r_excl_vaddr,
                                                r_excl_map, r_container_valid, r_container_data,
                                                r_entrypoint, r_bmap,
                                                r_l_way, r_s_way);
            call SaveContext_2();

            // some sanity checks.
            assert status_1 == status_2;
            assert current_mode_1 == current_mode_2;
            assert enclave_dead_1 == enclave_dead_2;
            current_mode := current_mode_1;
            enclave_dead := enclave_dead_2;
        } else {
            havoc e_proof_op;
            assume tap_proof_op_valid_in_enclave(e_proof_op);

            // trace_1
            call RestoreContext_1();
            call current_mode_1, load_addr_1, l_way_1, store_addr_1, store_data_1, s_way_1 :=
                            EnclaveStep(current_mode, eid, e_proof_op);
            call SaveContext_1();

            // trace_1
            call RestoreContext_2();
            call current_mode_2, load_addr_2, l_way_2, store_addr_2, store_data_2, s_way_2 :=
                            EnclaveStep(current_mode, eid, e_proof_op);
            call SaveContext_2();

            // some sanity checks.
            assert current_mode_1 == current_mode_2;
            current_mode := current_mode_1;

            // we assume that enclave/inputs and outputs are identical.
            assume (!e_excl_vaddr_1[load_addr_1] || !e_excl_vaddr_2[load_addr_2]) ==>
                       (load_addr_1 == load_addr_2 && l_way_1 == l_way_2 &&
                        cpu_addr_map_1[load_addr_1] == cpu_addr_map_2[load_addr_2]);
            assume (!e_excl_vaddr_1[store_addr_1] || !e_excl_vaddr_2[store_addr_2]) ==>
                       (store_addr_1 == store_addr_2 && store_data_1 == store_data_2 && s_way_1 == s_way_2 &&
                        cpu_addr_map_1[store_addr_1] == cpu_addr_map_2[store_addr_2]);
        }
    }
}
