implementation refinement_proof_step_load()
{
  var vaddr: vaddr_t;
  var tap_data, sanctum_data: word_t;
  var sanctum_exn: bool;
  var tap_exn: exception_t;
  var cpu_mode: riscv_mode_t;
  var valid: bool;
  var paddr: paddr_t;
  var acl: pte_acl_t;
  var hit: bool;
  var repl_way : cache_way_index_t;

  havoc vaddr;
  havoc cpu_mode; assume cpu_mode == cpu_mode_const; assume cpu_mode != RISCV_MODE_M;
  call valid, paddr, acl := translate(vaddr, riscv_access_read, cpu_mode, cpu_mode_pum_const, cpu_mode_mxr_const);
  call sanctum_data, sanctum_exn := RISCV_ISA_load(vaddr);
  assert valid <==> !sanctum_exn;
  assert !sanctum_exn ==> acl2read(ptbl_acl_map[select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(vaddr)]);
  if (!sanctum_exn) {
    havoc repl_way; assume valid_cache_way_index(repl_way);
    call tap_data, tap_exn, hit := load_va(vaddr, repl_way);
    assert (tap_exn == excp_none);
    assert (tap_data == sanctum_data);
  }
}

implementation refinement_proof_step_store()
{
  var vaddr: vaddr_t;
  var tap_data, sanctum_data: word_t;
  var sanctum_exn: bool;
  var tap_exn: exception_t;
  var cpu_mode: riscv_mode_t;
  var valid: bool;
  var paddr: paddr_t;
  var acl: pte_acl_t;
  var hit: bool;
  var repl_way : cache_way_index_t;

  havoc vaddr, sanctum_data;
  havoc cpu_mode; assume cpu_mode == cpu_mode_const; assume cpu_mode != RISCV_MODE_M;
  call valid, paddr, acl := translate(vaddr, riscv_access_write, cpu_mode, cpu_mode_pum_const, cpu_mode_mxr_const);
  call sanctum_exn := RISCV_ISA_store(vaddr, sanctum_data);
  assert valid <==> !sanctum_exn;
  if (!sanctum_exn) {
    havoc repl_way; assume valid_cache_way_index(repl_way);
    call tap_exn, hit := store_va(vaddr, sanctum_data, repl_way);
    assert (tap_exn == excp_none);
  }
}
