
implementation refinement_proof_step_init()
{
  call initialize_tap();
  call initialize_sanctum();
  // assume the page tables are related.
  assume (forall v : vaddr_t :: tap_addr_perm_r(cpu_addr_valid[v]) == acl2read(ptbl_acl_map[select_ppn(core_info_enclave_id, v, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(v)]));
  assume (forall v : vaddr_t :: tap_addr_perm_w(cpu_addr_valid[v]) == acl2write(ptbl_acl_map[select_ppn(core_info_enclave_id, v, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(v)]));
  assume (forall v : vaddr_t :: tap_addr_perm_x(cpu_addr_valid[v]) == acl2exec(ptbl_acl_map[select_ppn(core_info_enclave_id, v, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(v)]));
  assume (forall v : vaddr_t :: tap_addr_perm_v(cpu_addr_valid[v]) == acl2valid(ptbl_acl_map[select_ppn(core_info_enclave_id, v, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(v)]));
  assume (forall va: vaddr_t :: (untrusted_addr_map[va] == paddr2wpaddr(ptbl_addr_map[cpu_ptbr, vaddr2vpn(va)] ++ vaddr2offset(va))));
}
