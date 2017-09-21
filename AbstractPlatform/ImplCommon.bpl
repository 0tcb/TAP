procedure tap_addr_valid_proofs()
{
    // setting the present bit does not affect the axrw bits.
    assert (forall p : addr_perm_t :: tap_addr_perm_p(tap_set_addr_perm_p(p)));
    assert (forall p : addr_perm_t :: tap_addr_perm_a(tap_set_addr_perm_p(p)) == tap_addr_perm_a(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_x(tap_set_addr_perm_p(p)) == tap_addr_perm_x(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_r(tap_set_addr_perm_p(p)) == tap_addr_perm_r(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_w(tap_set_addr_perm_p(p)) == tap_addr_perm_w(p));
    // setting the a bit does not affect the pxrw bits.
    assert (forall p : addr_perm_t :: tap_addr_perm_a(tap_set_addr_perm_a(p)));
    assert (forall p : addr_perm_t :: tap_addr_perm_p(tap_set_addr_perm_a(p)) == tap_addr_perm_p(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_x(tap_set_addr_perm_a(p)) == tap_addr_perm_x(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_r(tap_set_addr_perm_a(p)) == tap_addr_perm_r(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_w(tap_set_addr_perm_a(p)) == tap_addr_perm_w(p));
    // setting the x bit does not affect parw.
    assert (forall p : addr_perm_t :: tap_addr_perm_x(tap_set_addr_perm_x(p)));
    assert (forall p : addr_perm_t :: tap_addr_perm_p(tap_set_addr_perm_x(p)) == tap_addr_perm_p(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_a(tap_set_addr_perm_x(p)) == tap_addr_perm_a(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_r(tap_set_addr_perm_x(p)) == tap_addr_perm_r(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_w(tap_set_addr_perm_x(p)) == tap_addr_perm_w(p));
    // setting the r bit does not affect paxw.
    assert (forall p : addr_perm_t :: tap_addr_perm_r(tap_set_addr_perm_r(p)));
    assert (forall p : addr_perm_t :: tap_addr_perm_p(tap_set_addr_perm_r(p)) == tap_addr_perm_p(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_a(tap_set_addr_perm_x(p)) == tap_addr_perm_a(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_x(tap_set_addr_perm_r(p)) == tap_addr_perm_x(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_w(tap_set_addr_perm_r(p)) == tap_addr_perm_w(p));
    // setting the w bit does not affect pax:.
    assert (forall p : addr_perm_t :: tap_addr_perm_w(tap_set_addr_perm_w(p)));
    assert (forall p : addr_perm_t :: tap_addr_perm_p(tap_set_addr_perm_w(p)) == tap_addr_perm_p(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_a(tap_set_addr_perm_x(p)) == tap_addr_perm_a(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_x(tap_set_addr_perm_w(p)) == tap_addr_perm_x(p));
    assert (forall p : addr_perm_t :: tap_addr_perm_r(tap_set_addr_perm_w(p)) == tap_addr_perm_r(p));
    // tap_addr_perm_eq
    assert (forall p1, p2 : addr_perm_t :: (tap_addr_perm_eq(p1, p2)) <==>
                                           (tap_addr_perm_bits(p1) == tap_addr_perm_bits(p2)));
}

implementation InitialHavoc()
    returns (current_mode : mode_t)
{
    var status            : enclave_op_result_t;
    var r_eid             : tap_enclave_id_t;
    var r_addr_valid      : addr_valid_t;
    var r_addr_map        : addr_map_t;
    var r_addr_excl       : excl_vaddr_t;
    var r_excl_map        : excl_map_t;
    var r_container_valid : container_valid_t;
    var r_container_data  : container_data_t;
    var r_entrypoint      : vaddr_t;
    var r_vaddr           : vaddr_t;
    var r_paddr           : wap_addr_t;
    var r_word            : word_t;
    var r_valid           : addr_perm_t;
    var r_excp            : exception_t;
    var repl_way          : cache_way_index_t;
    var done              : bool;
    var hit               : bool;

    call initialize_tap();
    current_mode := mode_untrusted;
    // and loop will run for a few iterations.
    done := false;

    while (!done)
        // CPU invariants.
        invariant (done ==> (cpu_enclave_id == tap_null_enc_id));
        // current pc invariants
        invariant (tap_addr_perm_x(cpu_addr_valid[cpu_pc]));
        invariant (cpu_owner_map[cpu_addr_map[cpu_pc]] == cpu_enclave_id);
        invariant (valid_enclave_id(cpu_enclave_id) || cpu_enclave_id == tap_null_enc_id);
        invariant (valid_enclave_id(cpu_enclave_id)) ==> (tap_enclave_metadata_addr_excl[cpu_enclave_id][cpu_pc]);
        // OS invariants.
        invariant (valid_enclave_id(cpu_enclave_id)) ==> (tap_addr_perm_x(untrusted_addr_valid[untrusted_pc]));
        invariant (valid_enclave_id(cpu_enclave_id)) ==> (cpu_owner_map[untrusted_addr_map[untrusted_pc]] == tap_null_enc_id);
        // CPU/enclave invariants.
        invariant (valid_enclave_id(cpu_enclave_id)==> tap_enclave_metadata_valid[cpu_enclave_id]);
        invariant (cpu_enclave_id != tap_blocked_enc_id);
        // enclave invariants.
        invariant (forall e : tap_enclave_id_t ::
                    !valid_enclave_id(e) ==> !tap_enclave_metadata_valid[e]);
        invariant (valid_enclave_id(cpu_enclave_id)) ==> 
                    tap_addr_perm_x(tap_enclave_metadata_addr_valid[cpu_enclave_id][cpu_pc]);
        invariant (valid_enclave_id(cpu_enclave_id)) ==> 
                    cpu_owner_map[tap_enclave_metadata_addr_map[cpu_enclave_id][cpu_pc]] == cpu_enclave_id;
        invariant (valid_enclave_id(cpu_enclave_id)) ==>
                    tap_addr_perm_x(
                        tap_enclave_metadata_addr_valid[cpu_enclave_id][tap_enclave_metadata_entrypoint[cpu_enclave_id]]);
        invariant (valid_enclave_id(cpu_enclave_id)) ==>
                    cpu_owner_map[tap_enclave_metadata_addr_map[cpu_enclave_id][tap_enclave_metadata_entrypoint[cpu_enclave_id]]] == cpu_enclave_id;
        invariant (forall e : tap_enclave_id_t ::
                    tap_enclave_metadata_valid[e] ==> 
                        tap_addr_perm_x(tap_enclave_metadata_addr_valid[e][tap_enclave_metadata_pc[e]]));
        invariant (forall e : tap_enclave_id_t ::
                    tap_enclave_metadata_valid[e] ==> 
                        tap_addr_perm_x(tap_enclave_metadata_addr_valid[e][tap_enclave_metadata_entrypoint[e]]));
        invariant (forall e : tap_enclave_id_t, v : vaddr_t ::
                    (tap_enclave_metadata_valid[e] && tap_enclave_metadata_addr_excl[e][v]) ==> 
                            tap_addr_perm_v(tap_enclave_metadata_addr_valid[e][v]));
        invariant (forall e : tap_enclave_id_t, v : vaddr_t ::
                    (tap_enclave_metadata_valid[e] && tap_enclave_metadata_addr_excl[e][v]) ==> 
                            (cpu_owner_map[tap_enclave_metadata_addr_map[e][v]] == e));
        invariant (forall e : tap_enclave_id_t ::
                    tap_enclave_metadata_valid[e] ==> 
                        tap_enclave_metadata_addr_excl[e][tap_enclave_metadata_pc[e]]);
        invariant (forall e : tap_enclave_id_t ::
                    tap_enclave_metadata_valid[e] ==> 
                        tap_enclave_metadata_addr_excl[e][tap_enclave_metadata_entrypoint[e]]);
        invariant (forall e : tap_enclave_id_t ::
                    tap_enclave_metadata_valid[e] ==> 
                        cpu_owner_map[tap_enclave_metadata_addr_map[e][tap_enclave_metadata_pc[e]]] == e);
        invariant (forall e : tap_enclave_id_t ::
                    tap_enclave_metadata_valid[e] ==> 
                        cpu_owner_map[tap_enclave_metadata_addr_map[e][tap_enclave_metadata_entrypoint[e]]] == e);
        // CPU/Enclave address map invariants.
        invariant (forall va : vaddr_t :: 
                    (cpu_enclave_id == tap_null_enc_id) ==> 
                        (cpu_addr_map[va] == untrusted_addr_map[va]));
        invariant (forall va : vaddr_t :: 
                    (cpu_enclave_id == tap_null_enc_id) ==> 
                        tap_addr_perm_eq(cpu_addr_valid[va], untrusted_addr_valid[va]));
        invariant (forall va : vaddr_t :: 
                    (cpu_enclave_id != tap_null_enc_id) ==> 
                        (cpu_addr_map[va] == tap_enclave_metadata_addr_map[cpu_enclave_id][va]));
        invariant (forall va : vaddr_t :: 
                    (cpu_enclave_id != tap_null_enc_id) ==> 
                        tap_addr_perm_eq(cpu_addr_valid[va], tap_enclave_metadata_addr_valid[cpu_enclave_id][va]));
        invariant  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                    (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                        (cpu_owner_map[pa] != e));
    {
        havoc r_eid;
        if(*) {
            havoc r_addr_valid, r_addr_map, r_excl_map;
            havoc r_container_valid, r_container_data, r_entrypoint;
            assume !r_excl_map[cpu_addr_map[cpu_pc]];
            call InitOSMem(r_container_valid, r_container_data);
            call status := launch(r_eid, r_addr_valid, r_addr_map, r_addr_excl, r_excl_map, r_entrypoint);
        } else if (*) {
            call status := enter(r_eid);
        } else if (*) {
            call status := exit();
        } else if (*) {
            call status := resume(r_eid);
        } else if (*) {
            call status := pause();
        } else if (*) {
            call status := destroy(r_eid);
        } else if (*) {
            havoc r_vaddr, r_word;
            havoc repl_way;
            assume valid_cache_way_index(repl_way);
            call r_excp, hit := store_va(r_vaddr, r_word, repl_way);
        } else if (*) {
            havoc cpu_pc;
            havoc cpu_regs;
            assume (tap_addr_perm_x(cpu_addr_valid[cpu_pc]));
            assume (cpu_enclave_id != tap_null_enc_id) ==> 
                        (tap_enclave_metadata_addr_excl[cpu_enclave_id][cpu_pc]);
            assume (cpu_owner_map[cpu_addr_map[cpu_pc]] == cpu_enclave_id);
        } else if (*) {
            if (cpu_enclave_id == tap_null_enc_id) {
                havoc r_valid, r_vaddr, r_paddr;
                assume r_vaddr != cpu_pc && r_vaddr != untrusted_pc;
                call set_addr_map(r_vaddr, r_paddr, r_valid);
            }
        } else if (*) {
            if (cpu_enclave_id == tap_null_enc_id) {
                done := true;
                assert cpu_enclave_id == tap_null_enc_id;
            }
        }
    }
}
