implementation refinement_proof_step_enter_enclave()
{
  var tid: thread_id_t, eid: enclave_id_t;
  var t_eid : tap_enclave_id_t;
  var api_result: api_result_t;
  var status: enclave_op_result_t;

  havoc eid, tid;
  call api_result := enter_enclave(eid, tid);
  if (api_result == monitor_ok) {
    t_eid := enclave_id_bv2int(eid);
    call status := enter(t_eid);
    assert core_info_enclave_id == eid;
    assert cpu_enclave_id == t_eid;
    assert (core_info_enclave_id != null_enclave_id);
    assert (cpu_enclave_id != tap_null_enc_id);
    assert (cpu_evbase == enclave_metadata_ev_base[eid]);
    assert (cpu_evmask == enclave_metadata_ev_mask[eid]);
    assert status == enclave_op_success;

    /*
    assert core_info_enclave_id == eid;
    assert cpu_enclave_id == t_eid;
    assert (core_info_enclave_id != null_enclave_id);
    assert (cpu_enclave_id != tap_null_enc_id);
    assert (forall va: vaddr_t, vpn : vpn_t :: 
                (in_enclave_mem(va, cpu_evbase, cpu_evmask) <==> 
                 tap_enclave_metadata_addr_excl[cpu_enclave_id][va]));
    assert (forall va: vaddr_t, vpn : vpn_t :: 
        tap_enclave_metadata_addr_excl[t_eid][va] ==> 
        tap_sanctum_perm_eq(tap_metadata_enclave_[va], ptbl_acl_map[cpu_eptbr, vpn]));
    assert (forall va: vaddr_t, vpn : vpn_t :: 
        (core_info_enclave_id != null_enclave_id            &&
         cpu_enclave_id != tap_null_enc_id                  && 
         vpn == vaddr2vpn(va)                               && 
         in_enclave_mem(va, cpu_evbase, cpu_evmask)         && 
         tap_enclave_metadata_addr_excl[cpu_enclave_id][va]) ==> 
        tap_sanctum_perm_eq(cpu_addr_valid[va], ptbl_acl_map[cpu_eptbr, vpn]));
      */
  }
}

implementation {:inline 1} refinement_proof_step_exit_enclave()
{
  var api_result: api_result_t;
  var status: enclave_op_result_t;

  call api_result := exit_enclave();
  if (api_result == monitor_ok) {
    call status := exit();
    assert status == enclave_op_success;
  }
}
