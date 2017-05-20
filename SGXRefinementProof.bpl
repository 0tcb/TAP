function {:inline} sgx_eid_to_tap_eid(e: wap_addr_t) : tap_enclave_id_t;
axiom (forall v1, v2: wap_addr_t :: v1 != v2 ==> sgx_eid_to_tap_eid(v1) != sgx_eid_to_tap_eid(v2));

procedure TAPSGXRefinement()
modifies cpu_owner_map,
         cpu_mem,
         cpu_addr_valid,
         cpu_addr_map,
         cpu_enclave_id,
         cpu_regs,
         cpu_pc,
         tap_enclave_metadata_valid,
         tap_enclave_metadata_addr_map,
         tap_enclave_metadata_addr_valid,
         tap_enclave_metadata_addr_excl,
         tap_enclave_metadata_entrypoint,
         tap_enclave_metadata_pc,
         tap_enclave_metadata_regs,
         tap_enclave_metadata_paused,
         tap_enclave_metadata_cache_conflict,
         cache_valid_map,
         cache_tag_map,
         untrusted_regs,
         untrusted_addr_map,
         untrusted_addr_valid,
         untrusted_pc;
modifies page_table_map,
         page_table_valid,
         curr_lp,
         xstate,
         lp_state,
         mem_secs,
         mem_tcs,
         mem_reg,
         epcm,
         arbitrary_write_count;

//TAP's invariants (i.e. all invariants that are not relational w.r.t. SGX)
requires (cpu_enclave_id == tap_null_enc_id) ==> ((cpu_addr_map == untrusted_addr_map) && 
                                                  (forall v : vaddr_t :: tap_addr_perm_eq(cpu_addr_valid[v], untrusted_addr_valid[v])));
requires ((cpu_enclave_id != tap_null_enc_id) ==> tap_enclave_metadata_valid[cpu_enclave_id]);
requires (cpu_enclave_id != tap_null_enc_id) ==> ((cpu_addr_map == tap_enclave_metadata_addr_map[cpu_enclave_id]) && (cpu_addr_valid == tap_enclave_metadata_addr_valid[cpu_enclave_id]));
requires (cpu_enclave_id != tap_null_enc_id) ==> (forall v : vaddr_t :: cpu_addr_map[v] == tap_enclave_metadata_addr_map[cpu_enclave_id][v]);
requires (cpu_enclave_id != tap_null_enc_id) ==> (forall v : vaddr_t :: tap_addr_perm_eq(cpu_addr_valid[v], tap_enclave_metadata_addr_valid[cpu_enclave_id][v]));
requires (forall pa : wap_addr_t, e : tap_enclave_id_t :: (e != tap_null_enc_id && !tap_enclave_metadata_valid[e]) ==> (cpu_owner_map[pa] != e));
//all mapped addresses within the evrange are private to that enclave
requires (forall v: vaddr_t, e : tap_enclave_id_t :: tap_enclave_metadata_valid[e] ==> 
  ((tap_enclave_metadata_addr_excl[e][v] && tap_addr_perm_v(tap_enclave_metadata_addr_valid[e][v])) ==> (cpu_owner_map[tap_enclave_metadata_addr_map[e][v]] == e)));
requires (forall pa: wap_addr_t, e: tap_enclave_id_t :: cpu_owner_map[pa] == e ==> tap_enclave_metadata_valid[e]);
requires (forall v: vaddr_t, pa: wap_addr_t, eid: tap_enclave_id_t :: tap_enclave_metadata_valid[eid] ==>
  tap_enclave_metadata_addr_excl[eid][v] ==> cpu_owner_map[cpu_addr_map[v]] == eid);

//SGX's invariants (i.e. all invariants that are not relational w.r.t. TAP)
requires curr_lp == 0; //only 1 CPU core is modeled in TAP
requires (forall pa: wap_addr_t :: Epcm_valid(epcm[pa]) ==> (is_epc_address(pa) && pageof_pa(pa) == pa));
requires (forall pa: wap_addr_t :: Secs_initialized(mem_secs[pa]) ==> pageof_pa(pa) == pa);
requires (forall e : wap_addr_t :: Secs_initialized(mem_secs[e]) <==> (Epcm_valid(epcm[e]) && Epcm_pt(epcm[e]) == pt_secs)); //mem_secs and epcm are in sync about which enclaves are alive
requires (forall pa: wap_addr_t :: (is_epc_address(pa) && pageof_pa(pa) == pa && Epcm_valid(epcm[pa])) ==>
  (pageof_pa(Epcm_enclavesecs(epcm[pa])) == Epcm_enclavesecs(epcm[pa]) && pageof_va(Epcm_enclaveaddress(epcm[pa])) == Epcm_enclaveaddress(epcm[pa])));
//all EPC pages for an enclave are mapping some addresses within the enclave's evrange
requires (forall e1, e2: wap_addr_t :: 
  (is_epc_address(e1) && is_epc_address(e2) && Epcm_valid(epcm[e1]) && Epcm_valid(epcm[e2])) ==>
    (Epcm_pt(epcm[e1]) == pt_secs && Epcm_pt(epcm[e2]) == pt_reg && Epcm_enclavesecs(epcm[e2]) == e1) ==> 
      (GE_va(Epcm_enclaveaddress(epcm[e2]), Secs_baseaddr(mem_secs[e1])) && 
       LT_va(PLUS_va(Epcm_enclaveaddress(epcm[e2]), 4095bv32), PLUS_va(Secs_baseaddr(mem_secs[e1]), Secs_size(mem_secs[e1])))));

//current enclave_ids are related
requires (cpu_enclave_id == tap_null_enc_id) <==> (!Lp_state_cr_enclave_mode(lp_state[curr_lp]));
requires ((cpu_enclave_id != tap_null_enc_id) ==> (cpu_enclave_id == sgx_eid_to_tap_eid(Lp_state_cr_active_secs(lp_state[curr_lp]))));
requires (Lp_state_cr_enclave_mode(lp_state[curr_lp]) ==> (cpu_enclave_id == sgx_eid_to_tap_eid(Lp_state_cr_active_secs(lp_state[curr_lp]))));

//both TAP and SGX have the same set of enclaves
requires (forall eid: wap_addr_t :: is_epc_address(eid) ==> (Secs_initialized(mem_secs[eid]) <==> tap_enclave_metadata_valid[sgx_eid_to_tap_eid(eid)]));
requires (forall eid: wap_addr_t :: is_epc_address(eid) ==> ((Epcm_valid(epcm[eid]) && Epcm_pt(epcm[eid]) == pt_secs) <==> (tap_enclave_metadata_valid[sgx_eid_to_tap_eid(eid)])));

//both TAP and SGX have the same evrange for their enclaves
requires (forall eid: wap_addr_t, v: vaddr_t :: 
  (is_epc_address(eid) && Secs_initialized(mem_secs[eid])) ==>
    (GE_va(v, Secs_baseaddr(mem_secs[eid])) && LT_va(v, PLUS_va(Secs_baseaddr(mem_secs[eid]), Secs_size(mem_secs[eid])))) ==>
      tap_enclave_metadata_addr_excl[sgx_eid_to_tap_eid(eid)][v]);

//physical memories are related
requires (forall pa: wap_addr_t :: cpu_mem[pa] == mem_reg[pa]);

//page tables are related
requires (forall va: vaddr_t :: (tap_addr_perm_v(cpu_addr_valid[va]) == page_table_valid[va]));
requires (forall va: vaddr_t :: page_table_valid[va] <==> (tap_addr_perm_r(cpu_addr_valid[va]) && tap_addr_perm_w(cpu_addr_valid[va]) && tap_addr_perm_x(cpu_addr_valid[va])));
requires (forall va: vaddr_t :: page_table_valid[va] ==> (cpu_addr_map[va] == page_table_map[va]));

//both TAP and SGX own the same regions
requires (forall pa: wap_addr_t :: Epcm_valid(epcm[pageof_pa(pa)]) ==> cpu_owner_map[pa] == sgx_eid_to_tap_eid(Epcm_enclavesecs(epcm[pageof_pa(pa)]))); 
requires (forall pa: wap_addr_t, e: wap_addr_t :: (cpu_owner_map[pa] == sgx_eid_to_tap_eid(e) && sgx_eid_to_tap_eid(e) != tap_null_enc_id) ==> 
  (Epcm_valid(epcm[pageof_pa(pa)]) && Epcm_enclavesecs(epcm[pageof_pa(pa)]) == e));
requires (forall e1 : wap_addr_t ::
  (is_epc_address(e1) && Epcm_valid(epcm[pageof_pa(e1)]) && Epcm_pt(epcm[pageof_pa(e1)]) == pt_reg) ==>
    (sgx_eid_to_tap_eid(Epcm_enclavesecs(epcm[pageof_pa(e1)])) == cpu_owner_map[e1] && cpu_owner_map[e1] != tap_null_enc_id));
requires (forall e1 : wap_addr_t :: Lp_state_cr_enclave_mode(lp_state[curr_lp]) ==>
  (is_epc_address(e1) && Epcm_valid(epcm[pageof_pa(e1)]) && Epcm_pt(epcm[pageof_pa(e1)]) == pt_reg) ==>
    (Epcm_enclavesecs(epcm[pageof_pa(e1)]) == Lp_state_cr_active_secs(lp_state[curr_lp])) ==>
      (cpu_owner_map[e1] == cpu_enclave_id && cpu_owner_map[e1] != tap_null_enc_id));
requires (forall a: wap_addr_t, e: tap_enclave_id_t :: cpu_owner_map[a] != tap_null_enc_id ==> 
  (is_epc_address(a) && Epcm_valid(epcm[pageof_pa(a)]) && Epcm_pt(epcm[pageof_pa(a)]) == pt_reg && sgx_eid_to_tap_eid(Epcm_enclavesecs(epcm[pageof_pa(a)])) == cpu_owner_map[a]));
{
  if (*) {
    call refinement_proof_step_load();
  } else if (*) {
    call refinement_proof_step_store();
  } else if (*) {
    call refinement_proof_step_ecreate();
  } else if (*) {
    call refinement_proof_step_eadd_reg();
  } else if (*) {
    call refinement_proof_step_eextend();
  } else if (*) {
    call refinement_proof_step_einit();
  } else if (*) {
    call refinement_proof_step_eenter();
  } else if (*) {
    call refinement_proof_step_eexit();
  } else if (*) {
    call refinement_proof_step_eremove();
  }
}

procedure {:inline 1} refinement_proof_step_load()
modifies cache_valid_map, cache_tag_map, cpu_addr_valid;
{
  var vaddr: vaddr_t;
  var sgx_api_result : sgx_api_result_t;
  var tap_data, sgx_data : word_t;
  var tap_exn: exception_t;
  var hit: bool;

  havoc vaddr;
  call sgx_data, sgx_api_result := sgx_load(vaddr);

  if (sgx_api_result == sgx_api_success) {
    call tap_data, tap_exn, hit := load_va(vaddr);
    assert (tap_exn == excp_none);
    assert (tap_data == sgx_data);
  }
}

procedure {:inline 1} refinement_proof_step_store()
modifies cpu_mem, cache_valid_map, cache_tag_map, cpu_addr_valid, arbitrary_write_count, mem_tcs, mem_secs, mem_reg;
{
  var vaddr: vaddr_t;
  var data: word_t;
  var sgx_api_result : sgx_api_result_t;
  var tap_exn: exception_t;
  var hit: bool;

  havoc vaddr, data;
  call sgx_api_result := sgx_store(vaddr, data);

  if (sgx_api_result == sgx_api_success) {
    call tap_exn, hit := store_va(vaddr, data);
    assert (tap_exn == excp_none);
  }
}

procedure {:inline 1} refinement_proof_step_ecreate()
modifies mem_secs, mem_reg, mem_tcs, epcm, arbitrary_write_count;
{
  var la: vaddr_t;
  var secs: secs_t;
  var sgx_api_result : sgx_api_result_t;
  
  havoc la, secs;
  call sgx_api_result := ecreate(la, secs);
  if (sgx_api_result == sgx_api_success) {
    assert true;
  }
}

procedure {:inline 1} refinement_proof_step_eadd_reg()
modifies mem_secs, mem_reg, mem_tcs, epcm, arbitrary_write_count;
{
  var rbx_linaddr: vaddr_t;
  var rbx_secs: vaddr_t;
  var rcx: vaddr_t;
  var r, w, x: bool;
  var d: mem_t;
  var sgx_api_result : sgx_api_result_t;

  havoc rbx_linaddr, rbx_secs, rcx, r, w, x, d;
  call sgx_api_result := eadd_reg(rbx_linaddr, rbx_secs, rcx, r, w, x, d);
  if (sgx_api_result == sgx_api_success) {
    assert true;
  }
}

procedure {:inline 1} refinement_proof_step_eextend()
modifies mem_secs, mem_reg, mem_tcs, arbitrary_write_count;
{
  var rcx: vaddr_t;
  var sgx_api_result : sgx_api_result_t;
  havoc rcx;
  call sgx_api_result := eextend(rcx); 
  if (sgx_api_result == sgx_api_success) {
    assert true;
  }
}

procedure {:inline 1} refinement_proof_step_einit()
modifies cpu_owner_map,
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
modifies mem_reg, mem_tcs, mem_secs, arbitrary_write_count;
{
  var sigstruct_signed: sigstruct_signed_t;
  var rcx: vaddr_t;
  var einittoken: einittoken_t;
  var sgx_api_result: sgx_api_result_t;
  var tap_eid : tap_enclave_id_t;
  var addr_valid: addr_valid_t;
  var addr_map: addr_map_t;
  var excl_vaddr : excl_vaddr_t;
  var excl_map: excl_map_t;
  var entrypoint: vaddr_t;
  var status: enclave_op_result_t;
  var secs: secs_t;

  havoc sigstruct_signed, rcx, einittoken;
  call sgx_api_result := einit(sigstruct_signed, rcx, einittoken);
  if (sgx_api_result == sgx_api_success) {
    tap_eid := sgx_eid_to_tap_eid(page_table_map[rcx]); assume tap_eid != tap_null_enc_id;
    secs := mem_secs[page_table_map[rcx]];

    assert !old(tap_enclave_metadata_valid[tap_eid]);

    //addr_valid specifies which page table entries are valid
    havoc addr_valid;
    assume (forall va: vaddr_t :: page_table_valid[va] <==> 
                                  (tap_addr_perm_r(addr_valid[va]) && tap_addr_perm_w(addr_valid[va]) && tap_addr_perm_x(addr_valid[va])));

    //addr_map sepcifies the address translation
    havoc addr_map;
    assume (forall va: vaddr_t :: page_table_valid[va] ==> (addr_map[va] == page_table_map[va]));

    havoc entrypoint;
    assume entrypoint == Secs_baseaddr(secs);
    // executable entrypoint.
    assume tap_addr_perm_x(addr_valid[entrypoint]);
    // exclusive entrypoint.
    assume excl_vaddr[entrypoint] && excl_map[addr_map[entrypoint]];

    havoc excl_vaddr;
    assume (forall va : vaddr_t ::
      (GE_va(va, Secs_baseaddr(secs)) && 
       LT_va(va, PLUS_va(Secs_baseaddr(secs), Secs_size(secs))))
      ==>
      excl_vaddr[va]);

    //excl_map specifies which physical regions is owned by this enclave
    havoc excl_map;
    assume (forall pa: wap_addr_t :: 
        (is_epc_address(pa) && 
         Epcm_valid(epcm[pageof_pa(pa)]) &&
         Epcm_pt(epcm[pageof_pa(pa)]) == pt_reg &&
         Epcm_enclavesecs(epcm[pageof_pa(pa)]) == page_table_map[rcx]) ==>
         excl_map[pa]);

    // FIXME: we have to prove these in the rest of the refinement.
    assume (forall v1, v2 : vaddr_t :: !vaddr_alias(excl_vaddr, addr_map, v1, v2)) &&
           (forall v : vaddr_t :: excl_vaddr[v] ==> excl_map[addr_map[v]]) && 
           (forall v : vaddr_t :: excl_vaddr[v] ==> tap_addr_perm_v(addr_valid[v]));

    call status := launch(tap_eid, addr_valid, addr_map, excl_vaddr, excl_map, entrypoint);
  }
}

procedure {:inline 1} refinement_proof_step_eenter()
modifies cpu_enclave_id,
         cpu_addr_map,
         cpu_addr_valid,
         cpu_pc,
         cpu_regs,
         untrusted_regs,
         untrusted_addr_map,
         untrusted_addr_valid,
         untrusted_pc;
modifies mem_reg, mem_tcs, mem_secs, lp_state, arbitrary_write_count;
{
  var rbx: vaddr_t;
  var sgx_api_result: sgx_api_result_t;
  var status: enclave_op_result_t;
  var tap_eid : tap_enclave_id_t;

  havoc rbx;
  call sgx_api_result := eenter(rbx);

  if (sgx_api_result == sgx_api_success) {
    tap_eid := sgx_eid_to_tap_eid(Epcm_enclavesecs(epcm[pageof_pa(page_table_map[rbx])]));
    call status := enter(tap_eid);
    assert status == enclave_op_success;
  }
}

procedure {:inline 1} refinement_proof_step_eexit()
modifies cpu_enclave_id,
         cpu_addr_map,
         cpu_addr_valid,
         cpu_regs,
         cpu_pc,
         tap_enclave_metadata_addr_map,
         tap_enclave_metadata_addr_valid,
         tap_enclave_metadata_pc,
         tap_enclave_metadata_paused;
modifies mem_reg, mem_tcs, mem_secs, xstate, lp_state, arbitrary_write_count;
{
  var sgx_api_result: sgx_api_result_t;
  var status: enclave_op_result_t;

  call sgx_api_result := eexit();

  if (sgx_api_result == sgx_api_success) {
    call status := exit();
    assert status == enclave_op_success;
  }
}

procedure {:inline 1} refinement_proof_step_eremove()
modifies cpu_mem, cpu_owner_map, tap_enclave_metadata_regs, tap_enclave_metadata_valid, tap_enclave_metadata_pc;
modifies epcm;
{
  var sgx_api_result: sgx_api_result_t;
  var status: enclave_op_result_t;
  var rcx: vaddr_t;
  var epc_pa: wap_addr_t;

  call sgx_api_result := eremove(rcx);

  if (sgx_api_result == sgx_api_success) {
    epc_pa := pageof_pa(page_table_map[rcx]);
    if (Epcm_pt(epcm[epc_pa]) == pt_secs) {
      call status := destroy(sgx_eid_to_tap_eid(page_table_map[pageof_va(rcx)]));
      assert status == enclave_op_success;
    }
  }
}


