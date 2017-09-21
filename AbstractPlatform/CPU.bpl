// -------------------------------------------------------------------- //
// CPU state                                                            //
// -------------------------------------------------------------------- //
var cpu_mem        : mem_t;
var cpu_regs       : regs_t;
var cpu_pc         : vaddr_t;
var cpu_enclave_id : tap_enclave_id_t;
var cpu_addr_valid : addr_valid_t;
var cpu_addr_map   : addr_map_t;
var cpu_owner_map  : owner_map_t;

// -------------------------------------------------------------------- //
// CPU uarch state                                                      //
// -------------------------------------------------------------------- //
const cpu_cache_enabled : bool;
const block_os_ev_read  : bool;

// -------------------------------------------------------------------- //
// State of the untrusted code (OS and its minions).                    //
// -------------------------------------------------------------------- //
// the untrusted pages
var untrusted_addr_valid : addr_valid_t;
var untrusted_addr_map   : addr_map_t;
var untrusted_regs       : regs_t;
var untrusted_pc         : vaddr_t;

// -------------------------------------------------------------------- //
// The enclaves in the system                                           //
// -------------------------------------------------------------------- //
var tap_enclave_metadata_valid          : tap_enclave_metadata_valid_t;
var tap_enclave_metadata_addr_map       : tap_enclave_metadata_addr_map_t;
var tap_enclave_metadata_addr_valid     : tap_enclave_metadata_addr_valid_t;
var tap_enclave_metadata_addr_excl      : tap_enclave_metadata_addr_excl_t;
var tap_enclave_metadata_num_threads    : tap_enclave_metadata_num_threads_t;
var tap_enclave_metadata_entrypoint     : tap_enclave_metadata_entrypoint_t;
var tap_enclave_metadata_pc             : tap_enclave_metadata_pc_t;
var tap_enclave_metadata_regs           : tap_enclave_metadata_regs_t;
var tap_enclave_metadata_paused         : tap_enclave_metadata_paused_t;
var tap_enclave_metadata_cache_conflict : tap_enclave_metadata_cache_conflict_t;

// -------------------------------------------------------------------- //
// Utility functions.                                                   //
// -------------------------------------------------------------------- //
const kzero_regs_t : regs_t;
axiom (forall ri : regindex_t :: kzero_regs_t[ri] == k0_word_t);

procedure initialize_tap();
  modifies cpu_enclave_id,
           cpu_addr_map,
           cpu_addr_valid,
           untrusted_addr_map,
           untrusted_addr_valid,
           untrusted_pc,
           untrusted_regs,
           cpu_pc,
           cpu_regs,
           cpu_owner_map,
           cpu_mem,
           cache_valid_map,
           tap_enclave_metadata_valid;
  ensures cpu_enclave_id == tap_null_enc_id;
  ensures cpu_addr_map == untrusted_addr_map;
  ensures cpu_addr_valid == untrusted_addr_valid;
  ensures cpu_pc == untrusted_pc;
  ensures cpu_regs == untrusted_regs;
  ensures (forall p : wap_addr_t :: cpu_mem[p] == k0_word_t);
  ensures (forall p : wap_addr_t :: cpu_owner_map[p] == tap_null_enc_id);
  ensures (forall e : tap_enclave_id_t :: !tap_enclave_metadata_valid[e]);
  ensures (tap_addr_perm_x(cpu_addr_valid[cpu_pc]));
  ensures cpu_cache_enabled ==>
            (forall i : cache_set_index_t, w : cache_way_index_t ::
                (valid_cache_set_index(i) && valid_cache_way_index(w)) ==> !cache_valid_map[i, w]);


procedure update_cache(pa : wap_addr_t);
  modifies cache_valid_map, cache_tag_map;


procedure {:inline 1} set_addr_map(va: vaddr_t, pa: wap_addr_t, valid: addr_perm_t)
  modifies untrusted_addr_valid, untrusted_addr_map,
           cpu_addr_valid, cpu_addr_map;
{
  if (cpu_enclave_id == tap_null_enc_id) {
    untrusted_addr_valid[va] := valid;
    cpu_addr_valid := untrusted_addr_valid;
    if (tap_addr_perm_v(valid)) {
        untrusted_addr_map[va] := pa;
        cpu_addr_map := untrusted_addr_map;
    }
  }
}

procedure {:inline 1} get_enclave_addr_map(
    /* eid */ eid : tap_enclave_id_t,
    /* va  */ va  : vaddr_t
) 
   returns (valid : addr_perm_t, paddr : wap_addr_t)
{
    // default values.
    valid := k0_addr_perm_t;
    paddr := k0_wap_addr_t;
    if (cpu_enclave_id == tap_null_enc_id   &&
        tap_enclave_metadata_valid[eid]) 
    {
        if (!block_os_ev_read || !tap_enclave_metadata_addr_excl[eid][va]) {
            valid := tap_enclave_metadata_addr_valid[eid][va];
            paddr := tap_enclave_metadata_addr_map[eid][va];
        }
    }
}

procedure {:inline 1} set_enclave_addr_map(
    /* eid   */ eid   : tap_enclave_id_t,
    /* va    */ va    : vaddr_t,
    /* valid */ valid : addr_perm_t,
    /* paddr */ paddr : wap_addr_t
) 
   returns (status : enclave_op_result_t)
   modifies tap_enclave_metadata_addr_valid;
   modifies tap_enclave_metadata_addr_map;
{
    // default values.
    if (cpu_enclave_id == tap_null_enc_id &&
        tap_enclave_metadata_valid[eid]) 
    {
        if (!tap_enclave_metadata_addr_excl[eid][va]) {
            tap_enclave_metadata_addr_valid[eid][va] := valid;
            tap_enclave_metadata_addr_map[eid][va] := paddr;
            status := enclave_op_success;
            return;
        }
    }
    status := enclave_op_invalid_arg;
}

procedure {:inline 1} fetch_va(vaddr : vaddr_t, repl_way : cache_way_index_t)
    returns (data: word_t, excp: exception_t, hit : bool)
    requires valid_cache_way_index(repl_way);
    modifies cpu_addr_valid, cache_valid_map, cache_tag_map;
{
    var paddr : wap_addr_t;
    var owner_eid : tap_enclave_id_t;
    var hit_way : cache_way_index_t;

    // default.
    data := k0_word_t;
    hit := false; 

    // translate VA -> PA.
    if (!tap_addr_perm_x(cpu_addr_valid[vaddr])) { 
        excp := excp_os_protection_fault; return; 
    }
    paddr := cpu_addr_map[vaddr];
    // are we not allowed to access this memory
    owner_eid := cpu_owner_map[paddr];
    if (owner_eid != tap_null_enc_id && owner_eid != cpu_enclave_id) {
        excp := excp_tp_protection_fault; return;
    }
    // update accessed bit.
    cpu_addr_valid[vaddr] := tap_set_addr_perm_a(cpu_addr_valid[vaddr]);
    // perform load.
    data := cpu_mem[paddr];
    excp := excp_none;
    // update cache.
    if (cpu_cache_enabled) { 
        call hit, hit_way := query_cache(paddr, repl_way); 
    }
}

procedure {:inline 1} load_va(vaddr : vaddr_t, repl_way : cache_way_index_t)
    returns (data: word_t, excp: exception_t, hit : bool)
    requires valid_cache_way_index(repl_way);
    modifies cache_valid_map, cache_tag_map, cpu_addr_valid;
{
    var paddr : wap_addr_t;
    var owner_eid : tap_enclave_id_t;
    var hit_way : cache_way_index_t;

    // default.
    data := k0_word_t;
    hit := false; 

    // translate VA -> PA.
    if (!tap_addr_perm_r(cpu_addr_valid[vaddr])) { 
        excp := excp_os_protection_fault; return; 
    }
    paddr := cpu_addr_map[vaddr];
    // are we not allowed to access this memory
    owner_eid := cpu_owner_map[paddr];
    if (owner_eid != tap_null_enc_id && owner_eid != cpu_enclave_id) {
        excp := excp_tp_protection_fault; return;
    }
    // update accessed bit.
    cpu_addr_valid[vaddr] := tap_set_addr_perm_a(cpu_addr_valid[vaddr]);
    // perform load.
    data := cpu_mem[paddr];
    excp := excp_none;
    // update cache.
    if (cpu_cache_enabled) { 
        call hit, hit_way := query_cache(paddr, repl_way); 
    }
}

procedure {:inline 1} store_va(vaddr : vaddr_t, data : word_t, repl_way : cache_way_index_t)
    returns (excp: exception_t, hit : bool)
    modifies cpu_mem;
    modifies cache_valid_map, cache_tag_map, cpu_addr_valid;
    requires valid_cache_way_index(repl_way);
    ensures (excp != excp_none ==> cpu_mem == old(cpu_mem));
{
    var paddr : wap_addr_t;
    var owner_eid : tap_enclave_id_t;
    var hit_way : cache_way_index_t;

    // default
    hit := false; 

    // translate VA -> PA.
    if (!tap_addr_perm_w(cpu_addr_valid[vaddr])) { 
        excp := excp_os_protection_fault; return; 
    }
    paddr := cpu_addr_map[vaddr];
    // are we not allowed to access this memory
    owner_eid := cpu_owner_map[paddr];
    if (owner_eid != tap_null_enc_id && owner_eid != cpu_enclave_id) {
        excp := excp_tp_protection_fault; return;
    }
    // update accessed bit.
    cpu_addr_valid[vaddr] := tap_set_addr_perm_a(cpu_addr_valid[vaddr]);
    // perform store.
    cpu_mem[paddr] := data;
    excp := excp_none;
    // update cache.
    if (cpu_cache_enabled) { 
        call hit, hit_way := query_cache(paddr, repl_way); 
    }
}

procedure modify_owner_map(
    /* enclave id   */  eid         : tap_enclave_id_t,
    /* new map      */  excl_paddr  : excl_map_t
)
    returns (status : enclave_op_result_t);
    modifies cpu_owner_map;
    modifies cpu_mem;

// -------------------------------------------------------------------- // 
// Helper functions                                                     // 
// -------------------------------------------------------------------- // 
function {:inline} vaddr_alias(
 /* addr valid */ av   : excl_vaddr_t,
 /* addr map   */ am   : addr_map_t,
 /* address    */ va1  : vaddr_t, va2 : vaddr_t) : bool
{ (va1 != va2 && av[va1] && av[va2] && am[va1] == am[va2]) }

// -------------------------------------------------------------------- //
// Launch an enclave                                                    //
// -------------------------------------------------------------------- //
procedure launch(
  /* eid.              */ eid             : tap_enclave_id_t,
  /* VA to PA. mapping */ addr_valid      : addr_valid_t,
  /* VA to PA mapping  */ addr_map        : addr_map_t,
  /* excl vaddr        */ excl_vaddr      : excl_vaddr_t,
  /* excl addr         */ excl_paddr      : excl_map_t,
  /* entrypoint.       */ entrypoint      : vaddr_t
)
    returns (status : enclave_op_result_t);

    modifies cpu_owner_map;
    modifies tap_enclave_metadata_valid;
    modifies tap_enclave_metadata_addr_map;
    modifies tap_enclave_metadata_addr_valid;
    modifies tap_enclave_metadata_addr_excl;
    modifies tap_enclave_metadata_entrypoint;
    modifies tap_enclave_metadata_pc;
    modifies tap_enclave_metadata_regs;
    modifies tap_enclave_metadata_paused;
    modifies tap_enclave_metadata_cache_conflict;

    //----------------------------------------------------------------------//
    // global TAP invariants.                                               //
    //----------------------------------------------------------------------//
    requires (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==>
                    (cpu_owner_map[pa] != e));
    ensures  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==>
                    (cpu_owner_map[pa] != e));

    //----------------------------------------------------------------------//
    // these postcondictions say that nothing changes if status != success  //
    //----------------------------------------------------------------------//
    ensures (status != enclave_op_success ==> cpu_owner_map == old(cpu_owner_map));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_valid == old(tap_enclave_metadata_valid));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_addr_map == old(tap_enclave_metadata_addr_map));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_addr_valid == old(tap_enclave_metadata_addr_valid));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_addr_excl == old(tap_enclave_metadata_addr_excl));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_entrypoint == old(tap_enclave_metadata_entrypoint));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_pc == old(tap_enclave_metadata_pc));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_regs == old(tap_enclave_metadata_regs));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_paused == old(tap_enclave_metadata_paused));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_cache_conflict == old(tap_enclave_metadata_cache_conflict));

    //----------------------------------------------------------------------//
    // these postconditions say that only entry [eid] changes in the maps.  //
    //----------------------------------------------------------------------//
    ensures (forall pa : wap_addr_t ::
                status == enclave_op_success ==>
                    (excl_paddr[pa] <==> cpu_owner_map[pa] == eid));
    ensures (forall pa : wap_addr_t ::
                status == enclave_op_success ==>
                (!excl_paddr[pa] ==> cpu_owner_map[pa] == old(cpu_owner_map)[pa]));
    ensures (forall pa : wap_addr_t ::
                status != enclave_op_success ==>
                    (cpu_owner_map[pa] == old(cpu_owner_map[pa])));
    ensures (forall e : tap_enclave_id_t ::
                (e != eid) ==> 
                    tap_enclave_metadata_valid[e] == old(tap_enclave_metadata_valid)[e]);
    ensures (forall e : tap_enclave_id_t ::
                (e != eid) ==> 
                    tap_enclave_metadata_addr_valid[e] == old(tap_enclave_metadata_addr_valid)[e]);
    ensures (forall e : tap_enclave_id_t ::
                (e != eid) ==> 
                    tap_enclave_metadata_addr_excl[e] == old(tap_enclave_metadata_addr_excl)[e]);
    ensures (forall e : tap_enclave_id_t ::
                (e != eid) ==> 
                    tap_enclave_metadata_addr_map[e] == old(tap_enclave_metadata_addr_map)[e]);
    ensures (forall e : tap_enclave_id_t ::
                (e != eid) ==> 
                    tap_enclave_metadata_pc[e] == old(tap_enclave_metadata_pc)[e]);
    ensures (forall e : tap_enclave_id_t ::
                (e != eid) ==> 
                    tap_enclave_metadata_entrypoint[e] == old(tap_enclave_metadata_entrypoint)[e]);
    ensures (forall e : tap_enclave_id_t ::
                (e != eid) ==> 
                    tap_enclave_metadata_regs[e] == old(tap_enclave_metadata_regs)[e]);
    ensures (forall e : tap_enclave_id_t ::
                (e != eid) ==> 
                    tap_enclave_metadata_paused[e] == old(tap_enclave_metadata_paused)[e]);
    ensures (forall e : tap_enclave_id_t ::
                (e != eid) ==> 
                    tap_enclave_metadata_cache_conflict[e] == old(tap_enclave_metadata_cache_conflict)[e]);
    
    //---------------------------------------------------------------------//
    // conditions which specify when we fail.                              //
    //---------------------------------------------------------------------//
    ensures
        ((cpu_enclave_id == tap_null_enc_id)                                                        &&   
         (valid_enclave_id(eid))                                                                    &&   
         (!old(tap_enclave_metadata_valid)[eid])                                                    &&   
         (tap_addr_perm_x(addr_valid[entrypoint]))                                                  &&   
         (excl_paddr[addr_map[entrypoint]])                                                         &&   
         (excl_vaddr[entrypoint])                                                                   &&
         (forall pa : wap_addr_t :: (excl_paddr[pa] ==> old(cpu_owner_map)[pa] == tap_null_enc_id)) &&   
         (forall v : vaddr_t :: excl_vaddr[v] ==> tap_addr_perm_v(addr_valid[v]))                   && 
         (forall v : vaddr_t :: excl_vaddr[v] ==> excl_paddr[addr_map[v]])                          &&
         (forall v1, v2 : vaddr_t :: !vaddr_alias(excl_vaddr, addr_map, v1, v2)))
    <==> (status == enclave_op_success);

    ensures (status == enclave_op_success || status == enclave_op_invalid_arg);

    //---------------------------------------------------------------------//
    // specify what changes when we succeed                                //
    //---------------------------------------------------------------------//
    ensures (status == enclave_op_success ==> (forall pa : wap_addr_t :: 
                (if excl_paddr[pa] then cpu_owner_map[pa] == eid
                                   else cpu_owner_map[pa] == old(cpu_owner_map)[pa])));
    ensures (status == enclave_op_success) ==> (forall pa : wap_addr_t :: 
            if excl_paddr[pa] then cpu_owner_map[pa] == eid
                            else cpu_owner_map[pa] == old(cpu_owner_map)[pa]);
    ensures (status == enclave_op_success) ==> (tap_enclave_metadata_valid[eid]);
    ensures (status == enclave_op_success) ==> (tap_enclave_metadata_pc[eid] == entrypoint);
    ensures (status == enclave_op_success) ==> (tap_enclave_metadata_entrypoint[eid] == entrypoint);
    ensures (status == enclave_op_success) ==> (!tap_enclave_metadata_paused[eid]);
    ensures (status == enclave_op_success) ==> (
                (exists p1, p2 : wap_addr_t :: cpu_owner_map[p1] == eid  && 
                                               cpu_owner_map[p2] != eid  && 
                                               paddr2set(p1) == paddr2set(p2))
                <==> tap_enclave_metadata_cache_conflict[eid]);
    ensures (status == enclave_op_success) ==> 
                (tap_enclave_metadata_regs[eid] == kzero_regs_t);
    ensures (status == enclave_op_success) ==> 
                (tap_enclave_metadata_addr_valid[eid] == addr_valid);
    ensures (status == enclave_op_success) ==> 
                (tap_enclave_metadata_addr_excl[eid] == excl_vaddr);
    ensures (status == enclave_op_success) ==> 
                (tap_enclave_metadata_addr_map[eid] == addr_map);

    // additional invariants that hold upon success.
    ensures (status == enclave_op_success) ==>
         (forall v1, v2 : vaddr_t :: 
            !vaddr_alias(tap_enclave_metadata_addr_excl[eid], 
                         tap_enclave_metadata_addr_map[eid], v1, v2));
    ensures (status == enclave_op_success) ==>
         (forall v : vaddr_t :: 
            tap_enclave_metadata_addr_excl[eid][v] ==>
            (cpu_owner_map[tap_enclave_metadata_addr_map[eid][v]] == eid));
    ensures (status == enclave_op_success) ==>
         (forall v : vaddr_t :: 
            tap_enclave_metadata_addr_excl[eid][v] ==>
            tap_addr_perm_v(tap_enclave_metadata_addr_valid[eid][v]));

// -------------------------------------------------------------------- //
// Enter an enclave                                                     //
// -------------------------------------------------------------------- //
procedure enter(eid: tap_enclave_id_t)
    returns (status : enclave_op_result_t);

    modifies cpu_enclave_id;
    modifies untrusted_regs;
    modifies cpu_addr_valid, untrusted_addr_valid;
    modifies cpu_addr_map, untrusted_addr_map;
    modifies cpu_pc, untrusted_pc;

    //----------------------------------------------------------------------//
    // global TAP invariants.                                               //
    //----------------------------------------------------------------------//
    requires (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));
    ensures  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));

    //----------------------------------------------------------------------//
    // conditions for success or failure.                                   //
    //----------------------------------------------------------------------//
    ensures ((valid_enclave_id(eid))                   &&
             (tap_enclave_metadata_valid[eid])         &&
             (old(cpu_enclave_id) == tap_null_enc_id)) ==> (status == enclave_op_success);
    ensures ((!valid_enclave_id(eid))                  ||
             (!tap_enclave_metadata_valid[eid])        ||
             (old(cpu_enclave_id) != tap_null_enc_id)) ==> (status == enclave_op_invalid_arg);
    ensures (status == enclave_op_success || status == enclave_op_invalid_arg);
                
    //----------------------------------------------------------------------//
    // nothing changes on failure.                                          //
    //----------------------------------------------------------------------//
    ensures (status != enclave_op_success ==> cpu_enclave_id == old(cpu_enclave_id));
    ensures (status != enclave_op_success ==> cpu_addr_valid == old(cpu_addr_valid));
    ensures (status != enclave_op_success ==> cpu_addr_map == old(cpu_addr_map));
    ensures (status != enclave_op_success ==> cpu_pc == old(cpu_pc));
    ensures (status != enclave_op_success ==> untrusted_regs == old(untrusted_regs));
    ensures (status != enclave_op_success ==> untrusted_addr_valid == old(untrusted_addr_valid));
    ensures (status != enclave_op_success ==> untrusted_addr_map == old(untrusted_addr_map));
    ensures (status != enclave_op_success ==> untrusted_pc == old(untrusted_pc));

    //----------------------------------------------------------------------//
    // state updates on success.                                            //
    //----------------------------------------------------------------------//
    ensures (status == enclave_op_success) ==> (untrusted_pc == old(cpu_pc));
    ensures (status == enclave_op_success) ==> (cpu_enclave_id == eid);
    ensures (status == enclave_op_success) ==> (cpu_pc == tap_enclave_metadata_entrypoint[eid]);
    ensures (status == enclave_op_success) ==> (untrusted_regs == old(cpu_regs));
    ensures (status == enclave_op_success) ==> (untrusted_addr_valid == old(cpu_addr_valid));
    ensures (status == enclave_op_success) ==> (untrusted_addr_map == old(cpu_addr_map));
    ensures (status == enclave_op_success) ==> (cpu_addr_valid == tap_enclave_metadata_addr_valid[eid]);
    ensures (status == enclave_op_success) ==> (cpu_addr_map == tap_enclave_metadata_addr_map[eid]);


// -------------------------------------------------------------------- //
// Resume an enclave                                                    //
// -------------------------------------------------------------------- //
procedure resume(eid: tap_enclave_id_t)
    returns (status : enclave_op_result_t);

    modifies cpu_enclave_id;
    modifies cpu_regs, untrusted_regs;
    modifies cpu_addr_valid, untrusted_addr_valid;
    modifies cpu_addr_map, untrusted_addr_map;
    modifies cpu_pc, untrusted_pc;

    //----------------------------------------------------------------------//
    // global TAP invariants.                                               //
    //----------------------------------------------------------------------//
    requires (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));
    ensures  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));

    //----------------------------------------------------------------------//
    // conditions for success or failure.                                   //
    //----------------------------------------------------------------------//
    ensures ((valid_enclave_id(eid))                      &&
             (tap_enclave_metadata_valid[eid])            && 
             (tap_enclave_metadata_paused[eid])           &&
             (old(cpu_enclave_id) == tap_null_enc_id))    ==> (status == enclave_op_success);
    ensures ((!valid_enclave_id(eid))                     ||
             (!tap_enclave_metadata_valid[eid])           || 
             (!tap_enclave_metadata_paused[eid])          ||
             (old(cpu_enclave_id) != tap_null_enc_id))    ==> (status == enclave_op_invalid_arg);
    ensures (status == enclave_op_success || status == enclave_op_invalid_arg);

    //----------------------------------------------------------------------//
    // nothing changes on failure.                                          //
    //----------------------------------------------------------------------//
    ensures (status != enclave_op_success ==> cpu_regs == old(cpu_regs));
    ensures (status != enclave_op_success ==> cpu_enclave_id == old(cpu_enclave_id));
    ensures (status != enclave_op_success ==> cpu_addr_valid == old(cpu_addr_valid));
    ensures (status != enclave_op_success ==> cpu_addr_map == old(cpu_addr_map));
    ensures (status != enclave_op_success ==> cpu_pc == old(cpu_pc));
    ensures (status != enclave_op_success ==> untrusted_regs == old(untrusted_regs));
    ensures (status != enclave_op_success ==> untrusted_addr_valid == old(untrusted_addr_valid));
    ensures (status != enclave_op_success ==> untrusted_addr_map == old(untrusted_addr_map));
    ensures (status != enclave_op_success ==> untrusted_pc == old(untrusted_pc));

    //----------------------------------------------------------------------//
    // state updates on success.                                            //
    //----------------------------------------------------------------------//
    ensures (status == enclave_op_success) ==> (untrusted_pc == old(cpu_pc));
    ensures (status == enclave_op_success) ==> (cpu_enclave_id == eid);
    ensures (status == enclave_op_success) ==> (cpu_pc == tap_enclave_metadata_pc[eid]);
    ensures (status == enclave_op_success) ==> (untrusted_regs == old(cpu_regs));
    ensures (status == enclave_op_success) ==> (untrusted_addr_valid == old(cpu_addr_valid));
    ensures (status == enclave_op_success) ==> (untrusted_addr_map == old(cpu_addr_map));
    ensures (status == enclave_op_success) ==> (cpu_regs == tap_enclave_metadata_regs[eid]);
    ensures (status == enclave_op_success) ==> (cpu_addr_valid == tap_enclave_metadata_addr_valid[eid]);
    ensures (status == enclave_op_success) ==> (cpu_addr_map == tap_enclave_metadata_addr_map[eid]);



// -------------------------------------------------------------------- //
// Exit an enclave.                                                     //
// -------------------------------------------------------------------- //
procedure exit()
    returns (status : enclave_op_result_t);

    modifies cpu_regs;
    modifies cpu_enclave_id;
    modifies cpu_addr_valid;
    modifies cpu_addr_map;
    modifies cpu_pc;
    modifies tap_enclave_metadata_addr_valid;
    modifies tap_enclave_metadata_addr_map;
    modifies tap_enclave_metadata_pc;
    modifies tap_enclave_metadata_paused;
    
    //----------------------------------------------------------------------//
    // global TAP invariants.                                               //
    //----------------------------------------------------------------------//
    requires (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));
    ensures  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));
               
    //----------------------------------------------------------------------//
    // success/failure conditions.                                          //
    //----------------------------------------------------------------------//
    ensures (old(cpu_enclave_id) == tap_null_enc_id) ==> (status == enclave_op_failed);
    ensures (old(cpu_enclave_id) != tap_null_enc_id) ==> (status == enclave_op_success);
    ensures (status == enclave_op_success || status == enclave_op_failed);

    //----------------------------------------------------------------------//
    // nothing changes on failure.                                          //
    //----------------------------------------------------------------------//
    ensures (status != enclave_op_success ==> cpu_regs == old(cpu_regs));
    ensures (status != enclave_op_success ==> cpu_enclave_id == old(cpu_enclave_id));
    ensures (status != enclave_op_success ==> cpu_addr_valid == old(cpu_addr_valid));
    ensures (status != enclave_op_success ==> cpu_addr_map == old(cpu_addr_map));
    ensures (status != enclave_op_success ==> cpu_pc == old(cpu_pc));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_addr_valid == old(tap_enclave_metadata_addr_valid));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_addr_map == old(tap_enclave_metadata_addr_map));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_pc == old(tap_enclave_metadata_pc));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_paused == old(tap_enclave_metadata_paused));
    // nothing except eid changes for paused, pc, addr_valid and addr_map
    ensures (forall e : tap_enclave_id_t :: 
        e != old(cpu_enclave_id) ==> 
            (tap_enclave_metadata_paused[e] == old(tap_enclave_metadata_paused)[e]));
    ensures (forall e : tap_enclave_id_t :: 
        e != old(cpu_enclave_id) ==> 
            (tap_enclave_metadata_pc[e] == old(tap_enclave_metadata_pc)[e]));
    ensures (forall e : tap_enclave_id_t ::
        e != old(cpu_enclave_id) ==>
            tap_enclave_metadata_addr_valid[e] == old(tap_enclave_metadata_addr_valid)[e]);
    ensures (forall e : tap_enclave_id_t ::
        e != old(cpu_enclave_id) ==>
            tap_enclave_metadata_addr_map[e] == old(tap_enclave_metadata_addr_map)[e]);

    //----------------------------------------------------------------------//
    // state updates on success.                                            //
    //----------------------------------------------------------------------//
    ensures (status == enclave_op_success) ==> (cpu_pc == old(untrusted_pc));
    ensures (status == enclave_op_success) ==> (cpu_enclave_id == tap_null_enc_id);
    ensures (status == enclave_op_success) ==> (!tap_enclave_metadata_paused[old(cpu_enclave_id)]);
    ensures (status == enclave_op_success) ==> 
            (tap_enclave_metadata_pc[old(cpu_enclave_id)] == tap_enclave_metadata_entrypoint[old(cpu_enclave_id)]);
    ensures (status == enclave_op_success) ==>
              (tap_enclave_metadata_addr_valid[old(cpu_enclave_id)] == old(cpu_addr_valid));
    ensures (status == enclave_op_success) ==>
              (tap_enclave_metadata_addr_map[old(cpu_enclave_id)] == old(cpu_addr_map));
    ensures (status == enclave_op_success) ==> (cpu_regs == untrusted_regs);
    ensures (status == enclave_op_success) ==> (cpu_addr_valid == untrusted_addr_valid);
    ensures (status == enclave_op_success) ==> (cpu_addr_map == untrusted_addr_map);


// -------------------------------------------------------------------- //
// Pause an enclave.                                                    //
// -------------------------------------------------------------------- //
procedure pause()
    returns (status : enclave_op_result_t);

    modifies cpu_regs;
    modifies cpu_enclave_id;
    modifies cpu_addr_valid;
    modifies cpu_addr_map;
    modifies cpu_pc;
    modifies tap_enclave_metadata_regs;
    modifies tap_enclave_metadata_addr_valid;
    modifies tap_enclave_metadata_addr_map;
    modifies tap_enclave_metadata_pc;
    modifies tap_enclave_metadata_paused;

    //----------------------------------------------------------------------//
    // global TAP invariants.                                               //
    //----------------------------------------------------------------------//
    requires (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));
    ensures  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));
    //----------------------------------------------------------------------//
    // success/failure conditions.                                          //
    //----------------------------------------------------------------------//
    ensures (old(cpu_enclave_id) == tap_null_enc_id) ==> (status == enclave_op_failed);
    ensures (old(cpu_enclave_id) != tap_null_enc_id) ==> (status == enclave_op_success);
    ensures (status == enclave_op_success || status == enclave_op_failed);
               
    //----------------------------------------------------------------------//
    // nothing changes on failure.                                          //
    //----------------------------------------------------------------------//
    ensures (status != enclave_op_success ==> cpu_regs == old(cpu_regs));
    ensures (status != enclave_op_success ==> cpu_enclave_id == old(cpu_enclave_id));
    ensures (status != enclave_op_success ==> cpu_addr_valid == old(cpu_addr_valid));
    ensures (status != enclave_op_success ==> cpu_addr_map == old(cpu_addr_map));
    ensures (status != enclave_op_success ==> cpu_pc == old(cpu_pc));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_regs == old(tap_enclave_metadata_regs));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_addr_valid == old(tap_enclave_metadata_addr_valid));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_addr_map == old(tap_enclave_metadata_addr_map));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_pc == old(tap_enclave_metadata_pc));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_paused == old(tap_enclave_metadata_paused));
    // nothing except eid changes for paused, pc, regs, addr_valid and addr_map
    ensures (forall e : tap_enclave_id_t :: 
        e != old(cpu_enclave_id) ==> 
            (tap_enclave_metadata_paused[e] == old(tap_enclave_metadata_paused)[e]));
    ensures (forall e : tap_enclave_id_t :: 
        e != old(cpu_enclave_id) ==> 
            (tap_enclave_metadata_pc[e] == old(tap_enclave_metadata_pc)[e]));
    ensures (forall e : tap_enclave_id_t ::
        e != old(cpu_enclave_id) ==>
            tap_enclave_metadata_regs[e] == old(tap_enclave_metadata_regs)[e]);
    ensures (forall e : tap_enclave_id_t ::
        e != old(cpu_enclave_id) ==>
            tap_enclave_metadata_addr_valid[e] == old(tap_enclave_metadata_addr_valid)[e]);
    ensures (forall e : tap_enclave_id_t ::
        e != old(cpu_enclave_id) ==>
            tap_enclave_metadata_addr_map[e] == old(tap_enclave_metadata_addr_map)[e]);

    //----------------------------------------------------------------------//
    // state updates on success.                                            //
    //----------------------------------------------------------------------//
    ensures (status == enclave_op_success) ==> (cpu_pc == old(untrusted_pc));
    ensures (status == enclave_op_success) ==> (cpu_enclave_id == tap_null_enc_id);
    ensures (status == enclave_op_success) ==> (tap_enclave_metadata_paused[old(cpu_enclave_id)]);
    ensures (status == enclave_op_success) ==> 
            (tap_enclave_metadata_pc[old(cpu_enclave_id)] == old(cpu_pc));
    ensures (status == enclave_op_success) ==>
            (tap_enclave_metadata_regs[old(cpu_enclave_id)] == old(cpu_regs));
    ensures (status == enclave_op_success) ==>
              (tap_enclave_metadata_addr_valid[old(cpu_enclave_id)] == old(cpu_addr_valid));
    ensures (status == enclave_op_success) ==>
              (tap_enclave_metadata_addr_map[old(cpu_enclave_id)] == old(cpu_addr_map));
    ensures (status == enclave_op_success) ==>
            (cpu_regs == untrusted_regs);
    ensures (status == enclave_op_success) ==>
            (cpu_addr_valid == untrusted_addr_valid);
    ensures (status == enclave_op_success) ==>
            (cpu_addr_map == untrusted_addr_map);


// -------------------------------------------------------------------- //
// Destroy an enclave                                                   //
// -------------------------------------------------------------------- //
procedure destroy(eid: tap_enclave_id_t)
    returns (status: enclave_op_result_t);

    modifies cpu_owner_map;
    modifies tap_enclave_metadata_regs;
    modifies tap_enclave_metadata_valid;
    modifies tap_enclave_metadata_pc;

    //----------------------------------------------------------------------//
    // global TAP invariants.                                               //
    //----------------------------------------------------------------------//
    requires (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));
    ensures  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));

    //----------------------------------------------------------------------//
    // success/failure conditions.                                          //
    //----------------------------------------------------------------------//
    ensures (!valid_enclave_id(eid)                 || 
             !old(tap_enclave_metadata_valid)[eid]  || 
             cpu_enclave_id != tap_null_enc_id) ==> (status == enclave_op_invalid_arg);
    ensures (valid_enclave_id(eid)                  && 
             old(tap_enclave_metadata_valid)[eid]   && 
             cpu_enclave_id == tap_null_enc_id) ==> (status == enclave_op_success);
    ensures (status == enclave_op_success || status == enclave_op_invalid_arg);

    //----------------------------------------------------------------------//
    // nothing changes on failure.                                          //
    //----------------------------------------------------------------------//
    ensures (status != enclave_op_success ==> cpu_owner_map == old(cpu_owner_map));
    ensures (status != enclave_op_success ==> cpu_pc == old(cpu_pc));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_regs == old(tap_enclave_metadata_regs));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_valid == old(tap_enclave_metadata_valid));
    ensures (status != enclave_op_success ==> tap_enclave_metadata_pc == old(tap_enclave_metadata_pc));
    // regs don't change except for eid.
    ensures (forall e : tap_enclave_id_t ::
                (e != eid) ==> tap_enclave_metadata_regs[e] == old(tap_enclave_metadata_regs)[e]);

    //----------------------------------------------------------------------//
    // status updates on success                                            //
    //----------------------------------------------------------------------//
    ensures (status == enclave_op_success) ==>
                (forall p : wap_addr_t ::
                    (if old(cpu_owner_map)[p] == eid
                        then (cpu_owner_map[p] == tap_blocked_enc_id)
                        else (cpu_owner_map[p] == old(cpu_owner_map)[p])));
    ensures (status == enclave_op_success) ==>
                (forall p : wap_addr_t ::
                    old(cpu_owner_map)[p] == eid ==>
                        (cpu_owner_map[p] == tap_blocked_enc_id));
    ensures (status == enclave_op_success) ==>
                (forall p : wap_addr_t ::
                    old(cpu_owner_map)[p] != eid ==> 
                        cpu_owner_map[p] == old(cpu_owner_map)[p]);
    ensures (status == enclave_op_success) ==>
                (forall e : tap_enclave_id_t :: 
                    tap_enclave_metadata_valid[e] == 
                        (if e == eid then false
                                     else old(tap_enclave_metadata_valid)[e]));
    ensures (status == enclave_op_success) ==>
                (forall e : tap_enclave_id_t :: 
                    tap_enclave_metadata_pc[e] == 
                        (if e == eid then k0_vaddr_t
                                     else old(tap_enclave_metadata_pc)[e]));
    ensures (status == enclave_op_success) ==>
                (tap_enclave_metadata_regs[eid] == kzero_regs_t);

// -------------------------------------------------------------------- //
// Block available memory.                                              //
// -------------------------------------------------------------------- //
procedure block_memory_region(bmap : excl_map_t)
   returns (status : enclave_op_result_t);
   modifies cpu_owner_map;
    //----------------------------------------------------------------------//
    // global TAP invariants.                                               //
    //----------------------------------------------------------------------//
    requires (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));
    ensures  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));

    // success condition.
    ensures ((forall p : wap_addr_t ::
                bmap[p] ==> (old(cpu_owner_map)[p] == tap_null_enc_id))
            <==> (status == enclave_op_success));
    ensures (status == enclave_op_success || status == enclave_op_invalid_arg);

    // effect on cpu_owner_map
    ensures (status == enclave_op_success) ==>
            (forall p : wap_addr_t :: 
                if bmap[p] 
                    then cpu_owner_map[p] == tap_blocked_enc_id
                    else cpu_owner_map[p] == old(cpu_owner_map)[p]);
    ensures (status != enclave_op_success) ==> 
                old(cpu_owner_map) == cpu_owner_map;
                 
     

   
// -------------------------------------------------------------------- //
// Reclaim blocked memory.                                              //
// -------------------------------------------------------------------- //
procedure release_blocked_memory(bmap : excl_map_t)
    returns (status : enclave_op_result_t);
    modifies cpu_owner_map;
    modifies cpu_mem;

    //----------------------------------------------------------------------//
    // global TAP invariants.                                               //
    //----------------------------------------------------------------------//
    requires (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));
    ensures  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));

    // success condition.
    ensures ((forall p : wap_addr_t ::
                bmap[p] ==> (old(cpu_owner_map)[p] == tap_blocked_enc_id))
            <==> (status == enclave_op_success));
    ensures (status == enclave_op_success || status == enclave_op_invalid_arg);

    // effect on cpu_owner_map
    ensures (status == enclave_op_success) ==>
            (forall p : wap_addr_t :: 
                if bmap[p] 
                    then (cpu_owner_map[p] == tap_null_enc_id && 
                          cpu_mem[p] == k0_word_t)
                    else (cpu_owner_map[p] == old(cpu_owner_map)[p] && 
                          cpu_mem[p] == old(cpu_mem[p])));
    ensures (status != enclave_op_success) ==> 
                (old(cpu_owner_map) == cpu_owner_map &&
                 old(cpu_mem) == cpu_mem);
