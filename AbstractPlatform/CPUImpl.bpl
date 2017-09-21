// -------------------------------------------------------------------- // 
// Initialize TAP.                                                      // 
// -------------------------------------------------------------------- // 
implementation initialize_tap()
{
  havoc untrusted_addr_map;
  havoc untrusted_addr_valid;
  havoc untrusted_addr_map;
  havoc untrusted_pc;
  havoc untrusted_regs;

  cpu_enclave_id := tap_null_enc_id;
  cpu_addr_map := untrusted_addr_map;
  cpu_addr_valid := untrusted_addr_valid;
  cpu_pc := untrusted_pc;
  cpu_regs := untrusted_regs;
  
  // memory is all zero'd out.
  havoc cpu_mem;
  assume (forall p : wap_addr_t :: cpu_mem[p] == k0_word_t);

  // no enclaves exist.
  havoc cpu_owner_map;
  assume (forall pa : wap_addr_t :: cpu_owner_map[pa] == tap_null_enc_id);
  havoc tap_enclave_metadata_valid;
  assume (forall e : tap_enclave_id_t :: !tap_enclave_metadata_valid[e]);
  // and that the PC is in sane state.
  assume (tap_addr_perm_x(cpu_addr_valid[cpu_pc]));
  assume (cpu_owner_map[cpu_addr_map[cpu_pc]] == cpu_enclave_id);

  if (cpu_cache_enabled) {
      call init_cache();
  }
}
// -------------------------------------------------------------------- // 
// Helper procedures                                                    // 
// -------------------------------------------------------------------- // 
procedure do_mappings_alias_v(
    /* valid */ addr_valid : excl_vaddr_t,
    /* map   */ addr_map   : addr_map_t
)
    returns (alias : bool);
    ensures (exists v1, v2 : vaddr_t :: vaddr_alias(addr_valid, addr_map, v1, v2)) 
            <==> alias;
    ensures (forall v1, v2 : vaddr_t :: !vaddr_alias(addr_valid, addr_map, v1, v2)) 
            <==> (!alias);
// TODO: Provide implementation for this.

procedure does_paddr_conflict(eid : tap_enclave_id_t, pa1 : wap_addr_t) 
  returns (conflict : bool)
  requires cpu_owner_map[pa1] == eid;
  ensures (exists p : wap_addr_t :: 
                cpu_owner_map[p] != eid && paddr2set(pa1) == paddr2set(p)) 
          <==> conflict;
{
  var pa : wap_addr_t;

  pa := k0_wap_addr_t;
  conflict := false;
  while (LT_wapa(pa, kmax_wap_addr_t))
    invariant (exists p : wap_addr_t :: 
                LT_wapa(p, pa) && cpu_owner_map[p] != eid && paddr2set(pa1) == paddr2set(p))
              <==> conflict;
  {
    if (cpu_owner_map[pa] != eid && paddr2set(pa1) == paddr2set(pa)) {
      conflict := true;
    }
    pa := PLUS_wapa(pa, k1_wap_addr_t);
  }
  if (cpu_owner_map[pa] != eid && paddr2set(pa1) == paddr2set(pa)) {
    conflict := true;
  }
}

procedure does_enclave_conflict(eid : tap_enclave_id_t)
  returns (conflict : bool)
  ensures (exists p1, p2 : wap_addr_t ::
                cpu_owner_map[p1] == eid  && 
                cpu_owner_map[p2] != eid  && 
                paddr2set(p1) == paddr2set(p2))
            <==> conflict;
{
  var pa : wap_addr_t;
  var pa_conflict : bool;

  pa := k0_wap_addr_t;
  conflict := false;
  while (LT_wapa(pa, kmax_wap_addr_t))
    invariant (exists p1, p2 : wap_addr_t ::
                  LT_wapa(p1, pa)           && 
                  cpu_owner_map[p1] == eid  && 
                  cpu_owner_map[p2] != eid  && 
                  paddr2set(p1) == paddr2set(p2))
              <==> conflict;
  {
    if (cpu_owner_map[pa] == eid) {
      call pa_conflict := does_paddr_conflict(eid, pa);
      conflict := conflict || pa_conflict;
    }
    pa := PLUS_wapa(pa, k1_wap_addr_t);
  }
  if (cpu_owner_map[pa] == eid) {
    call pa_conflict := does_paddr_conflict(eid, pa);
    conflict := conflict || pa_conflict;
  }
}

// -------------------------------------------------------------------- //
// Modify enclave's private pages.                                      //
// -------------------------------------------------------------------- //
implementation modify_owner_map(
    /* enclave id   */  eid         : tap_enclave_id_t,
    /* new map      */  excl_paddr  : excl_map_t
)
    returns (status : enclave_op_result_t)
{
    var va : vaddr_t;
    var pa : wap_addr_t;

    // must be called from outside the enclave.
    if (eid == tap_null_enc_id              ||
        cpu_enclave_id != tap_null_enc_id   ||
        !tap_enclave_metadata_valid[eid])
    {
        status := enclave_op_invalid_arg;
        return;
    }

    // can't unmap an address that is in evrange.
    va := k0_vaddr_t;
    while (LT_va(va, kmax_vaddr_t))
        invariant (forall v : vaddr_t :: 
            (LT_va(v, va) && 
             tap_enclave_metadata_addr_excl[eid][v] && 
             tap_addr_perm_v(tap_enclave_metadata_addr_valid[eid][v])) 
                ==> excl_paddr[tap_enclave_metadata_addr_map[eid][v]]);
    {
        if (tap_enclave_metadata_addr_excl[eid][va] && 
            tap_addr_perm_v(tap_enclave_metadata_addr_valid[eid][va]) &&
            !excl_paddr[tap_enclave_metadata_addr_map[eid][va]]) 
        {
            status := enclave_op_invalid_arg;
            return;
        }
        va := PLUS_va(va, k1_vaddr_t);
    }
    if (tap_enclave_metadata_addr_excl[eid][va] && 
        tap_addr_perm_v(tap_enclave_metadata_addr_valid[eid][va]) &&
        !excl_paddr[tap_enclave_metadata_addr_map[eid][va]]) 
    {
        status := enclave_op_invalid_arg;
        return;
    }
    va := PLUS_va(va, k1_vaddr_t);

    // sanity check.
    assert (forall v : vaddr_t :: 
             (tap_enclave_metadata_addr_excl[eid][v] && 
              tap_addr_perm_v(tap_enclave_metadata_addr_valid[eid][v])) 
                ==> excl_paddr[tap_enclave_metadata_addr_map[eid][v]]);

    // an address that differs between excl_paddr and cpu_owner must be
    // either owned by the enclave or the OS.
    pa := k0_wap_addr_t;
    while (LT_wapa(pa, kmax_wap_addr_t))
        invariant (forall p : wap_addr_t :: (LT_wapa(p, pa) && excl_paddr[p]) ==>
                    (cpu_owner_map[p] == tap_null_enc_id || cpu_owner_map[p] == eid));
    {
        if (excl_paddr[pa] && 
            (cpu_owner_map[pa] != tap_null_enc_id && cpu_owner_map[pa] != eid))
        {
            status := enclave_op_invalid_arg;
            return;
        }
        pa := PLUS_wapa(pa, k1_wap_addr_t);
    }
    if (excl_paddr[pa] && 
        (cpu_owner_map[pa] != tap_null_enc_id && cpu_owner_map[pa] != eid))
    {
        status := enclave_op_invalid_arg;
        return;
    }
    assert (forall p : wap_addr_t :: excl_paddr[p] ==>
                (cpu_owner_map[p] == tap_null_enc_id || cpu_owner_map[p] == eid));

    pa := k0_wap_addr_t;
    while (LT_wapa(pa, kmax_wap_addr_t))
        /*
        invariant (forall p : wap_addr_t :: 
                    if LT_wapa(p, pa)
                        then cpu_owner_map[p] == eid
                        else cpu_owner_map[p] == old(cpu_owner_map)[p]);
        invariant (forall p : wap_addr_t :: LT_wapa(p, pa) ==>
                    (excl_paddr[p] <==> (cpu_owner_map[p] == eid)));
        invariant (forall p : wap_addr_t :: 
                    if (LT_wapa(p, pa) && !excl_paddr[p] && old(cpu_owner_map)[p] == eid) 
                        then cpu_mem[p] == k0_word_t
                        else cpu_mem[p] == old(cpu_mem)[p]);
        */
    {
        if (excl_paddr[pa]) { cpu_owner_map[pa] := eid; } 
        else if (cpu_owner_map[pa] == eid) { 
            cpu_mem[pa] := k0_word_t;
            cpu_owner_map[pa] := tap_null_enc_id; 
        }
        pa := PLUS_wapa(pa, k1_wap_addr_t);
    }
    if (excl_paddr[pa]) { cpu_owner_map[pa] := eid; } 
    else if (cpu_owner_map[pa] == eid) { cpu_owner_map[pa] := tap_null_enc_id; }
    /*
    assert (forall p : wap_addr_t :: 
                (excl_paddr[p] <==> (cpu_owner_map[p] == eid)));
    */
}

// -------------------------------------------------------------------- //
// Launch an enclave                                                    //
// -------------------------------------------------------------------- //
implementation launch(
  /* eid.              */ eid             : tap_enclave_id_t,
  /* VA to PA. mapping */ addr_valid      : addr_valid_t,
  /* VA to PA mapping  */ addr_map        : addr_map_t,
  /* excl vaddr        */ excl_vaddr      : excl_vaddr_t,
  /* excl paddr        */ excl_paddr      : excl_map_t,
  /* entrypoint.       */ entrypoint      : vaddr_t
)
    returns (status : enclave_op_result_t)
{
    var i, k             : int;
    var mappings_alias_v : bool;
    var paddr            : wap_addr_t;
    var va               : vaddr_t;
    var cache_conflict   : bool;


    // ensure cpu mode is valid.
    if (cpu_enclave_id != tap_null_enc_id) {
        status := enclave_op_invalid_arg;
        return;
    }

    // ensure eid is valid.
    if (!valid_enclave_id(eid) || tap_enclave_metadata_valid[eid]) {
        status := enclave_op_invalid_arg;
        return;
    }

    // the entrypoint must be mapped and exclusive.
    if (!tap_addr_perm_x(addr_valid[entrypoint]) || 
        !excl_paddr[addr_map[entrypoint]]        ||
        !excl_vaddr[entrypoint])
    {
        status := enclave_op_invalid_arg;
        return;
    }

    // Ensure none of the paddr's are already exclusive.
    paddr := k0_wap_addr_t;
    while (LT_wapa(paddr, kmax_wap_addr_t))
        invariant (forall pa : wap_addr_t ::
            (LT_wapa(pa, paddr) && excl_paddr[pa]) ==>
                cpu_owner_map[pa] == tap_null_enc_id);
        invariant (forall pa : wap_addr_t ::
            (LT_wapa(pa, paddr) ==> cpu_owner_map[pa] != eid));
    {
        if (excl_paddr[paddr]) {
            if (cpu_owner_map[paddr] != tap_null_enc_id) {
                status := enclave_op_invalid_arg;
                return;
            }
        }
        if (cpu_owner_map[paddr] == eid) {
            status := enclave_op_invalid_arg;
            return;
        }
        paddr := PLUS_wapa(paddr, k1_wap_addr_t);
    }
    if ((excl_paddr[paddr] && cpu_owner_map[paddr] != tap_null_enc_id) ||
        (cpu_owner_map[paddr] == eid))
    {
        status := enclave_op_invalid_arg;
        return;
    }
    // check if the private addresses alias with anything else (paddr).
    call mappings_alias_v := do_mappings_alias_v(excl_vaddr, addr_map);
    if (mappings_alias_v) {
        status := enclave_op_invalid_arg;
        return;
    }

    // check if the private virt address map to a shared phys addr
    va := k0_vaddr_t;
    while (LT_va(va, kmax_vaddr_t))
        invariant (forall v : vaddr_t :: 
            (LT_va(v, va) && excl_vaddr[v]) ==> excl_paddr[addr_map[v]]);
        invariant (forall v : vaddr_t :: 
            (LT_va(v, va) && excl_vaddr[v]) ==> tap_addr_perm_v(addr_valid[v]));

    {
        if (excl_vaddr[va])
        {
            if(!excl_paddr[addr_map[va]] || !tap_addr_perm_v(addr_valid[va])) 
            {
                status := enclave_op_invalid_arg;
                return;
            }
        }
        va := PLUS_va(va, k1_vaddr_t);
    }
    if (excl_vaddr[va] && 
       (!excl_paddr[addr_map[va]] || !tap_addr_perm_v(addr_valid[va]))) 
    {
        status := enclave_op_invalid_arg;
        return;
    }

    // Set the CPU owner map.
    paddr := k0_wap_addr_t;
    while (LT_wapa(paddr, kmax_wap_addr_t))
        invariant (forall pa : wap_addr_t ::
            (LT_wapa(pa, paddr) && excl_paddr[pa]) ==> 
                cpu_owner_map[pa] == eid);
        invariant (forall pa : wap_addr_t ::
            (LT_wapa(pa, paddr) && !excl_paddr[pa]) ==> 
                cpu_owner_map[pa] == old(cpu_owner_map)[pa]);
        invariant (forall pa : wap_addr_t ::
            !LT_wapa(pa, paddr) ==> cpu_owner_map[pa] == old(cpu_owner_map)[pa]);
        invariant (forall e : tap_enclave_id_t, pa : wap_addr_t ::
                    (e != eid && e != tap_null_enc_id) ==> 
                        (cpu_owner_map[pa] == e) ==> (cpu_owner_map[pa] == old(cpu_owner_map)[pa]));
    {
        if (excl_paddr[paddr]) { cpu_owner_map[paddr] := eid; }
        paddr := PLUS_wapa(paddr, k1_wap_addr_t);
    }
    if (excl_paddr[paddr]) { cpu_owner_map[paddr] := eid; }

    // regs are zeroed out.
    call cache_conflict := does_enclave_conflict(eid);

    tap_enclave_metadata_valid[eid]          := true;
    tap_enclave_metadata_addr_map[eid]       := addr_map;
    tap_enclave_metadata_addr_valid[eid]     := addr_valid;
    tap_enclave_metadata_addr_excl[eid]      := excl_vaddr;
    tap_enclave_metadata_entrypoint[eid]     := entrypoint;
    tap_enclave_metadata_pc[eid]             := entrypoint;
    tap_enclave_metadata_regs[eid]           := kzero_regs_t;
    tap_enclave_metadata_paused[eid]         := false;
    tap_enclave_metadata_cache_conflict[eid] := cache_conflict;

    status := enclave_op_success;
}

// -------------------------------------------------------------------- //
// Enter an enclave                                                     //
// -------------------------------------------------------------------- //
implementation enter(eid: tap_enclave_id_t)
    returns (status : enclave_op_result_t)
{
    // no enclave  no enclave id is null.
    // enclave must be valid and not paused.
    // cpu must be ready to execute enclaves.
    if (!valid_enclave_id(eid)              ||
        !tap_enclave_metadata_valid[eid]    ||
        cpu_enclave_id != tap_null_enc_id)
    {
        status := enclave_op_invalid_arg;
        return;
    }

    status                      := enclave_op_success;
    // save context.
    untrusted_regs              := cpu_regs;
    untrusted_addr_valid        := cpu_addr_valid;
    untrusted_addr_map          := cpu_addr_map;
    untrusted_pc                := cpu_pc;
    // restore enclave context.
    cpu_enclave_id              := eid;
    cpu_addr_valid              := tap_enclave_metadata_addr_valid[eid];
    cpu_addr_map                := tap_enclave_metadata_addr_map[eid];
    cpu_pc                      := tap_enclave_metadata_entrypoint[eid];
}

// -------------------------------------------------------------------- //
// Resume an enclave                                                    //
// -------------------------------------------------------------------- //
implementation resume(eid: tap_enclave_id_t)
    returns (status : enclave_op_result_t)

{
    if (!valid_enclave_id(eid)              ||
        !tap_enclave_metadata_valid[eid]    || 
        !tap_enclave_metadata_paused[eid]   ||
        cpu_enclave_id != tap_null_enc_id)
    {
        status := enclave_op_invalid_arg;
        return;
    }

    // save context.
    untrusted_regs                   := cpu_regs;
    untrusted_addr_valid             := cpu_addr_valid;
    untrusted_addr_map               := cpu_addr_map;
    untrusted_pc                     := cpu_pc;
    // restore enclave context.
    cpu_enclave_id                   := eid;
    cpu_addr_valid                   := tap_enclave_metadata_addr_valid[eid];
    cpu_addr_map                     := tap_enclave_metadata_addr_map[eid];
    cpu_pc                           := tap_enclave_metadata_pc[eid];
    cpu_regs                         := tap_enclave_metadata_regs[eid];
    status                           := enclave_op_success;
}
// -------------------------------------------------------------------- //
// Exit an enclave.                                                     //
// -------------------------------------------------------------------- //
implementation exit()
    returns (status : enclave_op_result_t)
{
    var eid : tap_enclave_id_t;

    if (cpu_enclave_id == tap_null_enc_id) {
        status := enclave_op_failed;
        return;
    }

    status := enclave_op_success;

    eid                                  := cpu_enclave_id;
    tap_enclave_metadata_addr_valid[eid] := cpu_addr_valid;
    tap_enclave_metadata_addr_map[eid]   := cpu_addr_map;
    tap_enclave_metadata_pc[eid]         := tap_enclave_metadata_entrypoint[eid];
    tap_enclave_metadata_paused[eid]     := false;

    cpu_enclave_id := tap_null_enc_id;
    cpu_regs       := untrusted_regs;
    cpu_addr_valid := untrusted_addr_valid;
    cpu_addr_map   := untrusted_addr_map;
    cpu_pc         := untrusted_pc;
    status         := enclave_op_success;
}

// -------------------------------------------------------------------- //
// Pause an enclave.                                                    //
// -------------------------------------------------------------------- //
implementation pause()
    returns (status : enclave_op_result_t)
{
    var eid : tap_enclave_id_t;

    if (cpu_enclave_id == tap_null_enc_id) {
        status := enclave_op_failed;
        return;
    }
    status := enclave_op_success;

    eid                                  := cpu_enclave_id;
    tap_enclave_metadata_regs[eid]       := cpu_regs;
    tap_enclave_metadata_addr_valid[eid] := cpu_addr_valid;
    tap_enclave_metadata_addr_map[eid]   := cpu_addr_map;
    tap_enclave_metadata_pc[eid]         := cpu_pc;
    tap_enclave_metadata_paused[eid]     := true;

    cpu_enclave_id := tap_null_enc_id;
    cpu_regs       := untrusted_regs;
    cpu_addr_valid := untrusted_addr_valid;
    cpu_addr_map   := untrusted_addr_map;
    cpu_pc         := untrusted_pc;
    status         := enclave_op_success;
}

// -------------------------------------------------------------------- //
// Destroy an enclave                                                   //
// -------------------------------------------------------------------- //
implementation destroy(eid: tap_enclave_id_t)
    returns (status: enclave_op_result_t)

{
    var pa : wap_addr_t;
    // no enclave id is null.
    if (!valid_enclave_id(eid) || !tap_enclave_metadata_valid[eid] || cpu_enclave_id != tap_null_enc_id) {
        status := enclave_op_invalid_arg;
        return;
    }

    assert (cpu_enclave_id != eid);
    assert tap_enclave_metadata_valid[eid];

    // we have to clear out the enclaves registers and memory.
    pa := k0_wap_addr_t;
    while (LT_wapa(pa, kmax_wap_addr_t))
        invariant (forall p : wap_addr_t ::
                        LT_wapa(p, pa) ==>
                            (if old(cpu_owner_map)[p] == eid
                                then (cpu_owner_map[p] == tap_blocked_enc_id)
                                else (cpu_owner_map[p] == old(cpu_owner_map)[p])));

        invariant (forall p : wap_addr_t ::
                        (!LT_wapa(p, pa) ==>
                            (cpu_owner_map[p] == old(cpu_owner_map)[p])));
    {
        if (cpu_owner_map[pa] == eid) {
            cpu_owner_map[pa] := tap_blocked_enc_id;
        }
        pa := PLUS_wapa(pa, k1_wap_addr_t);
    }
    if (cpu_owner_map[kmax_wap_addr_t] == eid) {
        cpu_owner_map[kmax_wap_addr_t] := tap_blocked_enc_id;
    }
    assert (forall p : wap_addr_t ::
                    (if old(cpu_owner_map)[p] == eid
                        then (cpu_owner_map[p] == tap_blocked_enc_id)
                        else (cpu_owner_map[p] == old(cpu_owner_map)[p])));
    assert (forall p : wap_addr_t ::
                old(cpu_owner_map)[p] == eid ==>
                    (cpu_owner_map[p] == tap_blocked_enc_id));

    assert (forall p : wap_addr_t ::
                old(cpu_owner_map)[p] != eid ==> 
                    cpu_owner_map[p] == old(cpu_owner_map)[p]);
    assert (forall p : wap_addr_t ::
                (old(cpu_owner_map)[p] != eid) ==> cpu_mem[p] == old(cpu_mem)[p]);

    // and now we mark the enclave invalid.
    tap_enclave_metadata_valid[eid] := false;
    tap_enclave_metadata_regs[eid]  := kzero_regs_t;
    tap_enclave_metadata_pc[eid]    := k0_vaddr_t;

    status := enclave_op_success;
}

// -------------------------------------------------------------------- //
// Block available memory.                                              //
// -------------------------------------------------------------------- //
implementation block_memory_region(bmap : excl_map_t) 
    returns (status : enclave_op_result_t)
{
    var pa : wap_addr_t;

    // First make sure that all the addresses in bmap are blocked.
    pa := k0_wap_addr_t;
    while (LT_wapa(pa, kmax_wap_addr_t))
        invariant (forall p : wap_addr_t ::
                        (LT_wapa(p, pa) && bmap[p]) ==> (cpu_owner_map[p] == tap_null_enc_id));

    {
        if (bmap[pa] && cpu_owner_map[pa] != tap_null_enc_id) {
            status := enclave_op_invalid_arg;
            return;
        }
        pa := PLUS_wapa(pa, k1_wap_addr_t);
    }
    if (bmap[pa] && cpu_owner_map[pa] != tap_null_enc_id) {
        status := enclave_op_invalid_arg;
        return;
    }
    assert (forall p : wap_addr_t :: bmap[p] ==> (cpu_owner_map[p] == tap_null_enc_id));

    // Now go around clearing each address in bmap.
    pa := k0_wap_addr_t;
    while (LT_wapa(pa, kmax_wap_addr_t))
        invariant (forall p : wap_addr_t :: bmap[p] ==> 
                        (if (LT_wapa(p, pa))
                            then cpu_owner_map[p] == tap_blocked_enc_id
                            else cpu_owner_map[p] == tap_null_enc_id));
        invariant (forall p : wap_addr_t ::
                        if (LT_wapa(p, pa) && bmap[p])
                            then cpu_owner_map[p] == tap_blocked_enc_id
                            else cpu_owner_map[p] == old(cpu_owner_map[p]));
    {
        if (bmap[pa]) {
            cpu_owner_map[pa] := tap_blocked_enc_id;
        }
        pa := PLUS_wapa(pa, k1_wap_addr_t);
    }
    if (bmap[pa]) {
        cpu_owner_map[pa] := tap_blocked_enc_id;
    }
    assert (forall p : wap_addr_t :: 
            if bmap[p] 
               then (cpu_owner_map[p] == tap_blocked_enc_id) 
               else (cpu_owner_map[p] == old(cpu_owner_map)[p]));
    status := enclave_op_success;
}
// -------------------------------------------------------------------- //
// Reclaim blocked memory.                                              //
// -------------------------------------------------------------------- //
implementation release_blocked_memory(bmap : excl_map_t) 
    returns (status : enclave_op_result_t)
{
    var pa : wap_addr_t;

    // First make sure that all the addresses in bmap are blocked.
    pa := k0_wap_addr_t;
    while (LT_wapa(pa, kmax_wap_addr_t))
        invariant (forall p : wap_addr_t ::
                        (LT_wapa(p, pa) && bmap[p]) ==> (cpu_owner_map[p] == tap_blocked_enc_id));

    {
        if (bmap[pa] && cpu_owner_map[pa] != tap_blocked_enc_id) {
            status := enclave_op_invalid_arg;
            return;
        }
        pa := PLUS_wapa(pa, k1_wap_addr_t);
    }
    if (bmap[pa] && cpu_owner_map[pa] != tap_blocked_enc_id) {
        status := enclave_op_invalid_arg;
        return;
    }
    assert (forall p : wap_addr_t :: bmap[p] ==> (cpu_owner_map[p] == tap_blocked_enc_id));

    // Now go around clearing each address in bmap.
    pa := k0_wap_addr_t;
    while (LT_wapa(pa, kmax_wap_addr_t))
        invariant (forall p : wap_addr_t :: bmap[p] ==> 
                        (if (LT_wapa(p, pa))
                            then cpu_owner_map[p] == tap_null_enc_id
                            else cpu_owner_map[p] == tap_blocked_enc_id));
        invariant (forall p : wap_addr_t ::
                        if (LT_wapa(p, pa) && bmap[p])
                            then (cpu_owner_map[p] == tap_null_enc_id && cpu_mem[p] == k0_word_t)
                            else (cpu_owner_map[p] == old(cpu_owner_map[p]) && cpu_mem[p] == old(cpu_mem)[p]));

    {
        if (bmap[pa]) {
            cpu_owner_map[pa] := tap_null_enc_id;
            cpu_mem[pa] := k0_word_t;
        }
        pa := PLUS_wapa(pa, k1_wap_addr_t);
    }
    if (bmap[pa]) {
        cpu_owner_map[pa] := tap_null_enc_id;
        cpu_mem[pa] := k0_word_t;
    }
    assert (forall p : wap_addr_t :: 
            if bmap[p] 
               then (cpu_owner_map[p] == tap_null_enc_id && cpu_mem[p] == k0_word_t)
               else (cpu_owner_map[p] == old(cpu_owner_map)[p] && cpu_mem[p] == old(cpu_mem[p])));
    status := enclave_op_success;
}
