var cpu_mem_1                             : mem_t;
var cpu_mem_2                             : mem_t;
var cpu_regs_1                            : regs_t;
var cpu_regs_2                            : regs_t;
var cpu_pc_1                              : vaddr_t;
var cpu_pc_2                              : vaddr_t;
var cpu_enclave_id_1                      : tap_enclave_id_t;
var cpu_enclave_id_2                      : tap_enclave_id_t;
var cpu_addr_valid_1                      : addr_valid_t;
var cpu_addr_valid_2                      : addr_valid_t;
var cpu_addr_map_1                        : addr_map_t;
var cpu_addr_map_2                        : addr_map_t;
var cpu_owner_map_1                       : owner_map_t;
var cpu_owner_map_2                       : owner_map_t;
var cache_valid_map_1                     : cache_valid_map_t;
var cache_valid_map_2                     : cache_valid_map_t;
var cache_tag_map_1                       : cache_tag_map_t;
var cache_tag_map_2                       : cache_tag_map_t;
var untrusted_addr_valid_1                : addr_valid_t;
var untrusted_addr_valid_2                : addr_valid_t;
var untrusted_addr_map_1                  : addr_map_t;
var untrusted_addr_map_2                  : addr_map_t;
var untrusted_regs_1                      : regs_t;
var untrusted_regs_2                      : regs_t;
var untrusted_pc_1                        : vaddr_t;
var untrusted_pc_2                        : vaddr_t;
var tap_enclave_metadata_valid_1          : tap_enclave_metadata_valid_t;
var tap_enclave_metadata_valid_2          : tap_enclave_metadata_valid_t;
var tap_enclave_metadata_addr_map_1       : tap_enclave_metadata_addr_map_t;
var tap_enclave_metadata_addr_map_2       : tap_enclave_metadata_addr_map_t;
var tap_enclave_metadata_addr_valid_1     : tap_enclave_metadata_addr_valid_t;
var tap_enclave_metadata_addr_valid_2     : tap_enclave_metadata_addr_valid_t;
var tap_enclave_metadata_addr_excl_1      : tap_enclave_metadata_addr_excl_t;
var tap_enclave_metadata_addr_excl_2      : tap_enclave_metadata_addr_excl_t;
var tap_enclave_metadata_entrypoint_1     : tap_enclave_metadata_entrypoint_t;
var tap_enclave_metadata_entrypoint_2     : tap_enclave_metadata_entrypoint_t;
var tap_enclave_metadata_pc_1             : tap_enclave_metadata_pc_t;
var tap_enclave_metadata_pc_2             : tap_enclave_metadata_pc_t;
var tap_enclave_metadata_regs_1           : tap_enclave_metadata_regs_t;
var tap_enclave_metadata_regs_2           : tap_enclave_metadata_regs_t;
var tap_enclave_metadata_paused_1         : tap_enclave_metadata_paused_t;
var tap_enclave_metadata_paused_2         : tap_enclave_metadata_paused_t;
var tap_enclave_metadata_cache_conflict_1 : tap_enclave_metadata_cache_conflict_t;
var tap_enclave_metadata_cache_conflict_2 : tap_enclave_metadata_cache_conflict_t;

procedure {:inline 1} RestoreContext_1()
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
    cpu_mem                             := cpu_mem_1;
    cpu_regs                            := cpu_regs_1;
    cpu_pc                              := cpu_pc_1;
    cpu_enclave_id                      := cpu_enclave_id_1;
    cpu_addr_valid                      := cpu_addr_valid_1;
    cpu_addr_map                        := cpu_addr_map_1;
    cpu_owner_map                       := cpu_owner_map_1;
    cache_valid_map                     := cache_valid_map_1;
    cache_tag_map                       := cache_tag_map_1;
    untrusted_addr_valid                := untrusted_addr_valid_1;
    untrusted_addr_map                  := untrusted_addr_map_1;
    untrusted_regs                      := untrusted_regs_1;
    untrusted_pc                        := untrusted_pc_1;
    tap_enclave_metadata_valid          := tap_enclave_metadata_valid_1;
    tap_enclave_metadata_addr_map       := tap_enclave_metadata_addr_map_1;
    tap_enclave_metadata_addr_valid     := tap_enclave_metadata_addr_valid_1;
    tap_enclave_metadata_addr_excl      := tap_enclave_metadata_addr_excl_1;
    tap_enclave_metadata_entrypoint     := tap_enclave_metadata_entrypoint_1;
    tap_enclave_metadata_pc             := tap_enclave_metadata_pc_1;
    tap_enclave_metadata_regs           := tap_enclave_metadata_regs_1;
    tap_enclave_metadata_paused         := tap_enclave_metadata_paused_1;
    tap_enclave_metadata_cache_conflict := tap_enclave_metadata_cache_conflict_1;
}

procedure {:inline 1} SaveContext_1()
    modifies cpu_mem_1;
    modifies cpu_regs_1;
    modifies cpu_pc_1;
    modifies cpu_enclave_id_1;
    modifies cpu_addr_valid_1;
    modifies cpu_addr_map_1;
    modifies cpu_owner_map_1;
    modifies cache_valid_map_1, cache_tag_map_1;
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
{
    cpu_mem_1                             := cpu_mem;
    cpu_regs_1                            := cpu_regs;
    cpu_pc_1                              := cpu_pc;
    cpu_enclave_id_1                      := cpu_enclave_id;
    cpu_addr_valid_1                      := cpu_addr_valid;
    cpu_addr_map_1                        := cpu_addr_map;
    cpu_owner_map_1                       := cpu_owner_map;
    cache_valid_map_1                     := cache_valid_map;
    cache_tag_map_1                       := cache_tag_map;
    untrusted_addr_valid_1                := untrusted_addr_valid;
    untrusted_addr_map_1                  := untrusted_addr_map;
    untrusted_regs_1                      := untrusted_regs;
    untrusted_pc_1                        := untrusted_pc;
    tap_enclave_metadata_valid_1          := tap_enclave_metadata_valid;
    tap_enclave_metadata_addr_map_1       := tap_enclave_metadata_addr_map;
    tap_enclave_metadata_addr_valid_1     := tap_enclave_metadata_addr_valid;
    tap_enclave_metadata_addr_excl_1      := tap_enclave_metadata_addr_excl;
    tap_enclave_metadata_entrypoint_1     := tap_enclave_metadata_entrypoint;
    tap_enclave_metadata_pc_1             := tap_enclave_metadata_pc;
    tap_enclave_metadata_regs_1           := tap_enclave_metadata_regs;
    tap_enclave_metadata_paused_1         := tap_enclave_metadata_paused;
    tap_enclave_metadata_cache_conflict_1 := tap_enclave_metadata_cache_conflict;
}

procedure {:inline 2} RestoreContext_2()
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
    cpu_mem                             := cpu_mem_2;
    cpu_regs                            := cpu_regs_2;
    cpu_pc                              := cpu_pc_2;
    cpu_enclave_id                      := cpu_enclave_id_2;
    cpu_addr_valid                      := cpu_addr_valid_2;
    cpu_addr_map                        := cpu_addr_map_2;
    cpu_owner_map                       := cpu_owner_map_2;
    cache_valid_map                     := cache_valid_map_2;
    cache_tag_map                       := cache_tag_map_2;
    untrusted_addr_valid                := untrusted_addr_valid_2;
    untrusted_addr_map                  := untrusted_addr_map_2;
    untrusted_regs                      := untrusted_regs_2;
    untrusted_pc                        := untrusted_pc_2;
    tap_enclave_metadata_valid          := tap_enclave_metadata_valid_2;
    tap_enclave_metadata_addr_map       := tap_enclave_metadata_addr_map_2;
    tap_enclave_metadata_addr_valid     := tap_enclave_metadata_addr_valid_2;
    tap_enclave_metadata_addr_excl      := tap_enclave_metadata_addr_excl_2;
    tap_enclave_metadata_entrypoint     := tap_enclave_metadata_entrypoint_2;
    tap_enclave_metadata_pc             := tap_enclave_metadata_pc_2;
    tap_enclave_metadata_regs           := tap_enclave_metadata_regs_2;
    tap_enclave_metadata_paused         := tap_enclave_metadata_paused_2;
    tap_enclave_metadata_cache_conflict := tap_enclave_metadata_cache_conflict_2;
}

procedure {:inline 2} SaveContext_2()
    modifies cpu_mem_2;
    modifies cpu_regs_2;
    modifies cpu_pc_2;
    modifies cpu_enclave_id_2;
    modifies cpu_addr_valid_2;
    modifies cpu_addr_map_2;
    modifies cpu_owner_map_2;
    modifies cache_valid_map_2, cache_tag_map_2;
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
    cpu_mem_2                             := cpu_mem;
    cpu_regs_2                            := cpu_regs;
    cpu_pc_2                              := cpu_pc;
    cpu_enclave_id_2                      := cpu_enclave_id;
    cpu_addr_valid_2                      := cpu_addr_valid;
    cpu_addr_map_2                        := cpu_addr_map;
    cpu_owner_map_2                       := cpu_owner_map;
    cache_valid_map_2                     := cache_valid_map;
    cache_tag_map_2                       := cache_tag_map;
    untrusted_addr_valid_2                := untrusted_addr_valid;
    untrusted_addr_map_2                  := untrusted_addr_map;
    untrusted_regs_2                      := untrusted_regs;
    untrusted_pc_2                        := untrusted_pc;
    tap_enclave_metadata_valid_2          := tap_enclave_metadata_valid;
    tap_enclave_metadata_addr_map_2       := tap_enclave_metadata_addr_map;
    tap_enclave_metadata_addr_valid_2     := tap_enclave_metadata_addr_valid;
    tap_enclave_metadata_addr_excl_2      := tap_enclave_metadata_addr_excl;
    tap_enclave_metadata_entrypoint_2     := tap_enclave_metadata_entrypoint;
    tap_enclave_metadata_pc_2             := tap_enclave_metadata_pc;
    tap_enclave_metadata_regs_2           := tap_enclave_metadata_regs;
    tap_enclave_metadata_paused_2         := tap_enclave_metadata_paused;
    tap_enclave_metadata_cache_conflict_2 := tap_enclave_metadata_cache_conflict;
}

procedure HavocOSMem(excl_map : excl_map_t);
    modifies cpu_mem;
    ensures (forall p : wap_addr_t ::
                    (cpu_owner_map[p] != tap_null_enc_id || !excl_map[p])
                        ==> (cpu_mem[p] == old(cpu_mem)[p]));

procedure InitOSMem(container_valid : container_valid_t, container_data : container_data_t);
    modifies cpu_mem;
    ensures (forall p : wap_addr_t ::
                    if (cpu_owner_map[p] == tap_null_enc_id && container_valid[p])
                        then cpu_mem[p] == container_data[p]
                        else cpu_mem[p] == old(cpu_mem)[p]);

procedure InitialHavoc()
    returns (current_mode : mode_t);

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

    ensures (current_mode == mode_untrusted);
    //----------------------------------------------------------------------//
    // global TAP invariants.                                               //
    //----------------------------------------------------------------------//
    ensures (cpu_enclave_id == tap_null_enc_id);
    ensures  (forall pa : wap_addr_t, e : tap_enclave_id_t ::
                (valid_enclave_id(e) && !tap_enclave_metadata_valid[e]) ==> 
                    (cpu_owner_map[pa] != e));
    // current pc invariants
    ensures (tap_addr_perm_x(cpu_addr_valid[cpu_pc]));
    ensures (cpu_owner_map[cpu_addr_map[cpu_pc]] == cpu_enclave_id);
    // enclave invariants.
    ensures (forall e : tap_enclave_id_t :: !valid_enclave_id(e) ==> !tap_enclave_metadata_valid[e]);
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    tap_addr_perm_x(tap_enclave_metadata_addr_valid[e][tap_enclave_metadata_pc[e]]));
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    tap_addr_perm_x(tap_enclave_metadata_addr_valid[e][tap_enclave_metadata_entrypoint[e]]));
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    tap_enclave_metadata_addr_excl[e][tap_enclave_metadata_pc[e]]);
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    tap_enclave_metadata_addr_excl[e][tap_enclave_metadata_entrypoint[e]]);
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    cpu_owner_map[tap_enclave_metadata_addr_map[e][tap_enclave_metadata_pc[e]]] == e);
    ensures (forall e : tap_enclave_id_t ::
                tap_enclave_metadata_valid[e] ==> 
                    cpu_owner_map[tap_enclave_metadata_addr_map[e][tap_enclave_metadata_entrypoint[e]]] == e);
    // CPU/Enclave address map invariants.
    ensures (forall va : vaddr_t :: 
                (cpu_enclave_id == tap_null_enc_id) ==> 
                    (cpu_addr_map[va] == untrusted_addr_map[va]));
    ensures (forall va : vaddr_t :: 
                (cpu_enclave_id == tap_null_enc_id) ==> 
                    tap_addr_perm_eq(cpu_addr_valid[va], untrusted_addr_valid[va]));
    ensures (forall va : vaddr_t :: 
                (cpu_enclave_id != tap_null_enc_id) ==> 
                    (cpu_addr_map[va] == tap_enclave_metadata_addr_map[cpu_enclave_id][va]));
    ensures (forall va : vaddr_t :: 
                (cpu_enclave_id != tap_null_enc_id) ==> 
                    tap_addr_perm_eq(cpu_addr_valid[va], tap_enclave_metadata_addr_valid[cpu_enclave_id][va]));



// Uninterpreted functions to model deterministic computation.
function uf_cpu_r0_index(opcode : word_t) : regindex_t;
function uf_cpu_r1_index(opcode : word_t) : regindex_t;
function uf_cpu_r2_index(opcode : word_t) : regindex_t;
axiom (forall w : word_t :: valid_regindex(uf_cpu_r0_index(w)));
axiom (forall w : word_t :: valid_regindex(uf_cpu_r1_index(w)));
axiom (forall w : word_t :: valid_regindex(uf_cpu_r2_index(w)));

function uf_mem_load_vaddr(pc : vaddr_t, op : word_t, r1 : word_t, r2 : word_t) : vaddr_t;
function uf_mem_store_vaddr(pc : vaddr_t, op : word_t, l_data : word_t, r1 : word_t, r2 : word_t) : vaddr_t;
function uf_mem_store_data(pc : vaddr_t, op : word_t, l_data : word_t, r1 : word_t, r2 : word_t) : word_t;
function uf_cpu_pc(pc : vaddr_t, op : word_t, l_data : word_t, r1 : word_t, r2 : word_t) : vaddr_t;
function uf_cpu_result(pc : vaddr_t, op : word_t, l_data : word_t, r1 : word_t, r2 : word_t) : word_t;
function uf_observation(cpu_pc : vaddr_t, l_word : word_t, r_word : word_t, hit1 : bool, hit2 : bool, r_valid : addr_perm_t, r_paddr : wap_addr_t) : word_t;
function uf_observation_mem(cpu_pc : vaddr_t, l_word : word_t, r_word : word_t) : word_t;
function uf_observation_cache(hit1 : bool, hit2 : bool) : word_t;
function uf_observation_pt(r_valid : addr_perm_t, r_paddr : wap_addr_t) : word_t;

