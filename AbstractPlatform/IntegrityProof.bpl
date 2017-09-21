function uf_load_data(vaddr : vaddr_t, iter : int) : word_t;

// The computation performed by the enclave.
procedure {:inline 1} EnclaveComputation(iter : int)
    returns (vaddr : vaddr_t, paddr : wap_addr_t, data : word_t)

    modifies cpu_mem;
    modifies cpu_regs;
    modifies cpu_pc;
    modifies cache_valid_map, cache_tag_map, cpu_addr_valid;

    requires (tap_enclave_metadata_valid[cpu_enclave_id]);
    requires tap_addr_perm_x(cpu_addr_valid[cpu_pc]);
    requires cpu_owner_map[cpu_addr_map[cpu_pc]] == cpu_enclave_id;
{
    var r0, r1  : word_t;
    var rd      : regindex_t;
    var eid     : tap_enclave_id_t;
    var pc_pa   : wap_addr_t;
    var pc_op   : word_t;
    var l_vaddr : vaddr_t;
    var l_data  : word_t;
    var s_vaddr : vaddr_t;
    var s_data  : word_t;
    var excp    : exception_t;
    var hit     : bool;
    var way     : cache_way_index_t;

    eid := cpu_enclave_id;
    pc_pa := cpu_addr_map[cpu_pc];
    assert tap_enclave_metadata_addr_excl[eid][cpu_pc];
    assert tap_addr_perm_x(cpu_addr_valid[cpu_pc]);
    havoc way; assume valid_cache_way_index(way);
    call pc_op, excp, hit := fetch_va(cpu_pc, way);
    assert excp == excp_none;

    // two register sources.
    r0 := cpu_regs[uf_cpu_r0_index(pc_op)];
    r1 := cpu_regs[uf_cpu_r1_index(pc_op)];

    // load address and value.
    l_vaddr := uf_mem_load_vaddr(cpu_pc, pc_op, r0, r1);
    assume tap_addr_perm_r(cpu_addr_valid[l_vaddr]);
    if (tap_enclave_metadata_addr_excl[eid][l_vaddr]) {
        assert cpu_owner_map[cpu_addr_map[l_vaddr]] == eid;
        havoc way; assume valid_cache_way_index(way);
        call l_data, excp, hit := load_va(l_vaddr, way);
        assert excp == excp_none;
    } else {
        hit := false;
        excp := excp_none;
        l_data := uf_load_data(l_vaddr, iter);
    }

    // get data to store to mem.
    s_vaddr := uf_mem_store_vaddr(cpu_pc, pc_op, l_data, r0, r1);
    s_data := uf_mem_store_data(cpu_pc, pc_op, l_data, r0, r1);
    vaddr := s_vaddr;
    paddr := cpu_addr_map[s_vaddr];
    data := s_data;
    // update mem.
    assume tap_addr_perm_w(cpu_addr_valid[s_vaddr]);
    if (tap_enclave_metadata_addr_excl[eid][s_vaddr]) {
        assert (cpu_owner_map[cpu_addr_map[s_vaddr]] == eid);
        havoc way; assume valid_cache_way_index(way);
        call excp, hit := store_va(s_vaddr, s_data, way);
        assert excp == excp_none;
    }

    // update pc.
    cpu_pc := uf_cpu_pc(cpu_pc, pc_op, l_data, r0, r1);
    assume tap_addr_perm_x(cpu_addr_valid[cpu_pc]);
    assume tap_enclave_metadata_addr_excl[eid][cpu_pc];
    assert cpu_owner_map[cpu_addr_map[cpu_pc]] == eid;
    // update regs.
    rd := uf_cpu_r2_index(pc_op);
    cpu_regs[rd] := uf_cpu_result(cpu_pc, pc_op, l_data, r0, r1);
}

procedure {:inline 1} IntegrityAdversarialStep(
    /* mode       */ mode       : mode_t,
    /* EuT        */ eid        : tap_enclave_id_t,
    /* Adversary  */ r_eid      : tap_enclave_id_t,
    /* args       */ r_regs     : regs_t,
    /* operation  */ op         : tap_proof_op_t
)

    returns (current_mode : mode_t, enclave_dead : bool)

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
    var status            : enclave_op_result_t;
    var r_addr_valid      : addr_valid_t;
    var r_addr_map        : addr_map_t;
    var r_excl_vaddr      : excl_vaddr_t;
    var r_excl_map        : excl_map_t;
    var r_container_valid : container_valid_t;
    var r_container_data  : container_data_t;
    var r_entrypoint      : vaddr_t;
    var r_vaddr           : vaddr_t;
    var r_valid           : addr_perm_t;
    var r_excp            : exception_t;
    var r_paddr           : wap_addr_t;
    var r_word            : word_t;
    var r_bmap            : excl_map_t;
    var hit               : bool;
    var way               : cache_way_index_t;

    // the "default" value which may be overwritten by enter/resume
    current_mode := mode;
    // the "default" value which may be overwritten by destroy.
    enclave_dead := false;

    if (op == tap_proof_op_launch) {            
        // launch
        call InitOSMem(r_container_valid, r_container_data);
        call status := launch(r_eid, r_addr_valid, r_addr_map, 
                              r_excl_vaddr, r_excl_map, r_entrypoint);
        assert (r_eid == eid) ==> (status != enclave_op_success);
    } else if (op == tap_proof_op_enter) {      
        // enter
        cpu_regs := r_regs;
        call status := enter(r_eid);
        // mode == mode_enclave means we are in trace_2.
        assert (mode == mode_enclave ==> status == enclave_op_success);
        if (status == enclave_op_success && r_eid == eid) { 
            current_mode := mode_enclave; 
        }
    } else if (op == tap_proof_op_resume) {     
        // resume
        call status := resume(r_eid);
        // mode == mode_enclave means we are in trace_2.
        assert (mode == mode_enclave ==> status == enclave_op_success);
        if (status == enclave_op_success && r_eid == eid) { 
            current_mode := mode_enclave; 
        }
    } else if (op == tap_proof_op_exit) {       
        // exit
        call status := exit();
    } else if (op == tap_proof_op_pause) {      
        // pause.
        call status := pause();
    } else if (op == tap_proof_op_destroy) {    
        // destroy.
        call status := destroy(r_eid);
        if (r_eid == eid && status == enclave_op_success) {
            enclave_dead := true;
        }
    } else if (op == tap_proof_op_release) {
        call status := release_blocked_memory(r_bmap);
    } else if (op == tap_proof_op_block) {
        call status := block_memory_region(r_bmap);
    } else if (op == tap_proof_op_compute) {    
        // some adversarial computation
        if (*) {
            havoc r_vaddr, r_word;
            havoc way; assume valid_cache_way_index(way);
            call r_excp, hit := store_va(r_vaddr, r_word, way);
        } else if (*) {
            havoc cpu_regs, cpu_pc;
        } else if (*) {
            // update "page" table map.
            havoc r_vaddr, r_paddr, r_valid;
            cpu_addr_valid[r_vaddr] := r_valid;
            cpu_addr_map[r_vaddr] := r_paddr;
        } else if (*) {
            havoc r_vaddr, r_paddr, r_valid;
            call status := set_enclave_addr_map(r_eid, r_vaddr, r_valid, r_paddr);
        }
    }
}

procedure {:inline 1} IntegrityEnclaveStep(
    /* what operation?  */  op : tap_proof_op_t, 
    /* which iteration? */  iter : int
)
    returns (next_mode : mode_t, vaddr : vaddr_t, paddr : wap_addr_t, data : word_t)

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
    modifies tap_enclave_metadata_entrypoint;
    modifies tap_enclave_metadata_pc;
    modifies tap_enclave_metadata_regs;
    modifies tap_enclave_metadata_paused;
    modifies tap_enclave_metadata_cache_conflict;
{
    var status : enclave_op_result_t;
    assert tap_proof_op_valid_in_enclave(op);

    vaddr := k0_vaddr_t;
    paddr := k0_wap_addr_t;
    data := k0_word_t;

    // in enclave-mode:
    if (op == tap_proof_op_compute) {
        call vaddr, paddr, data := EnclaveComputation(iter);
        next_mode := mode_enclave;
    } else if (op == tap_proof_op_pause) {
        call status := pause();
        assert status == enclave_op_success;
        next_mode := mode_untrusted;
    } else if (op == tap_proof_op_exit) {
        call status := exit();
        assert status == enclave_op_success;
        next_mode := mode_untrusted;
    }
}

procedure ProveIntegrity()
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
    var eid, r_eid                                    : tap_enclave_id_t;
    var status                                        : enclave_op_result_t;
    var e_addr_valid                                  : addr_valid_t;
    var e_addr_map                                    : addr_map_t;
    var e_excl_vaddr                                  : excl_vaddr_t;
    var e_excl_map                                    : excl_map_t;
    var e_container_data                              : container_data_t;
    var e_entrypoint                                  : vaddr_t;
    var e_proof_op, r_proof_op                        : tap_proof_op_t;
    var r_regs                                        : regs_t;
    var current_mode_1, current_mode_2, current_mode  : mode_t;
    var enclave_dead                                  : bool;
    var r_paddr                                       : wap_addr_t;
    var r_word                                        : word_t;
    var vaddr_1, vaddr_2                              : vaddr_t;
    var paddr_1, paddr_2                              : wap_addr_t;
    var data_1, data_2                                : word_t;
    var iter                                          : int;

    // launch the same enclave in both traces.
    call RestoreContext_1();
    call current_mode_1 := InitialHavoc();
    call InitOSMem(e_excl_map, e_container_data);
    call status := launch(eid, e_addr_valid, e_addr_map, e_excl_vaddr, e_excl_map, e_entrypoint);
    assume status == enclave_op_success;
    call SaveContext_1();

    // trace_2.
    call RestoreContext_2();
    call current_mode_2 := InitialHavoc();
    call InitOSMem(e_excl_map, e_container_data);
    call status := launch(eid, e_addr_valid, e_addr_map, e_excl_vaddr, e_excl_map, e_entrypoint);
    assume status == enclave_op_success;
    call SaveContext_2();

    // sanity check.
    assert current_mode_1 == mode_untrusted;
    assert current_mode_2 == mode_untrusted;
    current_mode := current_mode_1;

    // main loop.
    enclave_dead := false;
    while (!enclave_dead)
        //----------------------------------------------------------------------//
        // global TAP invariants.                                               //
        //----------------------------------------------------------------------//
        invariant  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                    (valid_enclave_id(e) && !tap_enclave_metadata_valid_1[e]) ==> 
                        (cpu_owner_map_1[pa] != e));
        invariant  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                    (valid_enclave_id(e) && !tap_enclave_metadata_valid_2[e]) ==> 
                        (cpu_owner_map_2[pa] != e));
        // eid is valid.
        invariant valid_enclave_id(eid); 
        invariant !enclave_dead ==>
                    (tap_enclave_metadata_valid_1[eid] && tap_enclave_metadata_valid_2[eid]);
        // cpu_enclave_id is never blocked_enclave_id
        invariant (cpu_enclave_id_1 != tap_blocked_enc_id);
        invariant (cpu_enclave_id_2 != tap_blocked_enc_id);
        // the entrypoint always has an executable vaddr -> paddr mapping.
        invariant !enclave_dead ==>
                    tap_addr_perm_x(tap_enclave_metadata_addr_valid_1[eid][tap_enclave_metadata_entrypoint_1[eid]]);
        invariant !enclave_dead ==>
                    tap_addr_perm_x(tap_enclave_metadata_addr_valid_2[eid][tap_enclave_metadata_entrypoint_2[eid]]);
        invariant !enclave_dead ==>
                    tap_enclave_metadata_addr_excl_1[eid][tap_enclave_metadata_entrypoint_1[eid]];
        invariant !enclave_dead ==>
                    tap_enclave_metadata_addr_excl_2[eid][tap_enclave_metadata_entrypoint_2[eid]];
        // the pc always has an executable vaddr -> paddr mapping. 
        invariant !enclave_dead ==>
                    tap_addr_perm_x(tap_enclave_metadata_addr_valid_1[eid][tap_enclave_metadata_pc_1[eid]]);
        invariant !enclave_dead ==>
                    tap_addr_perm_x(tap_enclave_metadata_addr_valid_2[eid][tap_enclave_metadata_pc_2[eid]]);
        invariant !enclave_dead ==>
                    tap_enclave_metadata_addr_excl_1[eid][tap_enclave_metadata_pc_1[eid]];
        invariant !enclave_dead ==>
                    tap_enclave_metadata_addr_excl_2[eid][tap_enclave_metadata_pc_2[eid]];
        // the cpu_owner_map and enclave's excl_map are consistent.
        invariant (forall pa: wap_addr_t :: 
                    !enclave_dead ==> (cpu_owner_map_1[pa] == eid <==> e_excl_map[pa]));
        invariant (forall pa: wap_addr_t :: 
                    !enclave_dead ==> (cpu_owner_map_2[pa] == eid <==> e_excl_map[pa]));
        invariant (!enclave_dead) ==>
                     (tap_enclave_metadata_addr_excl_1[eid] == e_excl_vaddr);
        invariant (!enclave_dead) ==>
                     (tap_enclave_metadata_addr_excl_2[eid] == e_excl_vaddr);
        // permission bits are the same.
        invariant (forall v : vaddr_t :: (!enclave_dead && e_excl_vaddr[v]) ==>
                     (tap_enclave_metadata_addr_valid_1[eid][v] == tap_enclave_metadata_addr_valid_2[eid][v]));
        // the two vaddr->paddr maps are the same.
        invariant (forall va : vaddr_t :: (!enclave_dead && e_excl_vaddr[va]) ==>
                     (tap_enclave_metadata_addr_map_1[eid][va] == e_addr_map[va]));
        invariant (forall va : vaddr_t :: (!enclave_dead && e_excl_vaddr[va]) ==>
                     (tap_enclave_metadata_addr_map_2[eid][va] == e_addr_map[va]));
        // excl_vaddrs are excl_paddrs.
        invariant (forall v : vaddr_t, p : wap_addr_t :: (!enclave_dead && e_excl_vaddr[v] && p == e_addr_map[v]) ==> 
                        (cpu_owner_map_1[p] == eid));
        invariant (forall v : vaddr_t, p : wap_addr_t :: (!enclave_dead && e_excl_vaddr[v] && p == e_addr_map[v]) ==> 
                        (cpu_owner_map_2[p] == eid));
        // if an address is exclusive, it is the same for both enclaves. 
        invariant (forall pa : wap_addr_t :: !enclave_dead ==>
                     e_excl_map[pa] ==> (cpu_mem_1[pa] == cpu_mem_2[pa]));
        // the two PCs are the same.
        invariant !enclave_dead ==> 
                    (tap_enclave_metadata_pc_1[eid] == tap_enclave_metadata_pc_2[eid]);
        // the two entrypoints are the same.
        invariant !enclave_dead ==> 
                    (tap_enclave_metadata_entrypoint_1[eid] == tap_enclave_metadata_entrypoint_2[eid]);
        // the two enclaves are paused in the same way.
        invariant !enclave_dead ==> 
                    (tap_enclave_metadata_paused_1[eid] == tap_enclave_metadata_paused_2[eid]);
        // the two registers are the same.
        invariant (forall ri : regindex_t :: !enclave_dead ==>
                      (tap_enclave_metadata_regs_1[eid][ri] == tap_enclave_metadata_regs_2[eid][ri]));
        // invariants about the states of the CPUs.
        // are we in attacker mode?
        invariant (current_mode == mode_untrusted) ==> (cpu_enclave_id_1 != eid);
        invariant (current_mode == mode_untrusted) ==> (cpu_enclave_id_2 == tap_null_enc_id);
        // if we are in trusted mode, we mean our enclave. 
        invariant (current_mode == mode_enclave ==> 
                    (cpu_enclave_id_1 == eid  && cpu_enclave_id_2 == eid));
        // the CPU state is also the same in trusted mode.
        invariant (current_mode == mode_enclave ==> cpu_pc_1 == cpu_pc_2);
        invariant (current_mode == mode_enclave ==> tap_addr_perm_x(cpu_addr_valid_1[cpu_pc_1]));
        invariant (current_mode == mode_enclave ==> tap_addr_perm_x(cpu_addr_valid_2[cpu_pc_2]));
        invariant (current_mode == mode_enclave ==> tap_enclave_metadata_addr_excl_1[eid][cpu_pc_1]);
        invariant (current_mode == mode_enclave ==> tap_enclave_metadata_addr_excl_2[eid][cpu_pc_2]);
        invariant (current_mode == mode_enclave ==> cpu_owner_map_1[cpu_addr_map_1[cpu_pc_1]] == eid);
        invariant (current_mode == mode_enclave ==> cpu_owner_map_2[cpu_addr_map_2[cpu_pc_2]] == eid);
        // if we are in trusted mode, then metadata and CPU state are the same.
        invariant (forall ri : regindex_t ::
                    (current_mode == mode_enclave) ==>
                        (cpu_regs_1[ri] == cpu_regs_2[ri]));
        // This states that the two traces update addr_valid in the same way.
        invariant (forall va : vaddr_t ::
                    (current_mode == mode_enclave && e_excl_vaddr[va]) ==>
                        (cpu_addr_valid_1[va] == cpu_addr_valid_2[va]));
        // But note cpu_addr_valid may differ from the tap_enclave_metadata_addr_valid because 
        // the accessed bit is set in the form.
        invariant (forall va : vaddr_t ::
                    (current_mode == mode_enclave) ==>
                        tap_addr_perm_eq(tap_enclave_metadata_addr_valid_1[eid][va], cpu_addr_valid_1[va]));
        invariant (forall va : vaddr_t ::
                    (current_mode == mode_enclave) ==>
                        tap_addr_perm_eq(tap_enclave_metadata_addr_valid_2[eid][va], cpu_addr_valid_2[va]));
        invariant (forall va : vaddr_t ::
                    (current_mode == mode_enclave && e_excl_vaddr[va]) ==>
                        (e_addr_map[va] == cpu_addr_map_1[va]));
        invariant (forall va : vaddr_t ::
                    (current_mode == mode_enclave && e_excl_vaddr[va]) ==>
                        (e_addr_map[va] == cpu_addr_map_2[va]));
    {
        havoc r_eid, r_proof_op, e_proof_op, r_regs;
        if (current_mode == mode_untrusted) {
            assume tap_proof_op_valid(r_proof_op);

            // execute the operation in trace_1
            call RestoreContext_1();
            call current_mode, enclave_dead := IntegrityAdversarialStep(
                    current_mode, eid, r_eid, r_regs, r_proof_op);
            call SaveContext_1();

            // if the mode changed, we need to do this in trace_2
            call RestoreContext_2();
            if (current_mode == mode_enclave) {
                call current_mode, enclave_dead := IntegrityAdversarialStep(
                        current_mode, eid, r_eid, r_regs, r_proof_op);
                // sanity check.
                assert current_mode == mode_enclave;
                assert !enclave_dead;
            }
            call SaveContext_2();
        } else if (current_mode == mode_enclave) {
            havoc iter;
            assume tap_proof_op_valid_in_enclave(e_proof_op);

            // enclave step in trace_1
            call RestoreContext_1();
            call current_mode, vaddr_1, paddr_1, data_1 := IntegrityEnclaveStep(
                                                            e_proof_op, iter);
            call SaveContext_1();

            // enclave step in trace_2
            call RestoreContext_2();
            call current_mode, vaddr_2, paddr_2, data_2 := IntegrityEnclaveStep(
                                                            e_proof_op, iter);
            call SaveContext_2();

            assert vaddr_1 == vaddr_2;
            assert data_1 == data_2;
        }
    }
}
