implementation translate(
    vaddr: vaddr_t,
    access: riscv_access_t,
    cpu_mode: riscv_mode_t,
    cpu_mode_pum: bool,
    cpu_mode_mxr: bool)
returns (valid: bool, paddr: paddr_t, acl: pte_acl_t)
{
  call valid, paddr, acl := AbstractSanctum_translate(vaddr, access, cpu_mode, cpu_mode_pum, cpu_mode_mxr);
}


implementation create_page_table_mapping(ptbr: ppn_t, vaddr: vaddr_t, paddr: paddr_t, acl: pte_acl_t)
    returns (success : bool)
{
  call success := AbstractSanctum_create_page_table_mapping(ptbr, vaddr, paddr, acl);
}
