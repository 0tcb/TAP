implementation AbstractSanctum_translate(
    vaddr: vaddr_t,
    access: riscv_access_t,
    cpu_mode: riscv_mode_t,
    cpu_mode_pum: bool,
    cpu_mode_mxr: bool
)
    returns (valid: bool, paddr: paddr_t, acl: pte_acl_t)
{

    var t_valid: bool;
    var supervisor: bool;

    var paddr_region: region_t;
    var t_ptbr: ppn_t;
    var t_drbmap: bitmap_t;
    var t_parbase: paddr_t;
    var t_parmask: paddr_t;
    var r_selector: bool;
    var not_in_pa_range: bool;
    var valid_bmap: bool;

    t_ptbr := select_ppn(core_info_enclave_id,
                            vaddr, cpu_evbase, cpu_evmask,
                            cpu_eptbr, cpu_ptbr);
    t_drbmap := select_drbmap(core_info_enclave_id,
                                vaddr, cpu_evbase, cpu_evmask,
                                cpu_edrbmap, cpu_drbmap);
    t_parbase := select_paddr(core_info_enclave_id,
                                vaddr, cpu_evbase, cpu_evmask,
                                cpu_eparbase, cpu_parbase);
    t_parmask := select_paddr(core_info_enclave_id,
                                vaddr, cpu_evbase, cpu_evmask,
                                cpu_eparmask, cpu_parmask);

    call t_valid, paddr, acl := AbstractRISCV_translate(t_ptbr, access, vaddr);
    if (!t_valid) {
      valid := false;
      return;
    } else {
      valid_bmap := read_bitmap(t_drbmap, dram_region_for(paddr)) == 1bv1;
      not_in_pa_range  := AND_pa(paddr,t_parmask) != t_parbase;
      supervisor := cpu_mode == RISCV_MODE_S;
      valid := acl_valid(acl, access, supervisor, cpu_mode_pum, cpu_mode_mxr)
               && valid_bmap && not_in_pa_range;
    }
}

//
// Abstract load page table. Simply updates the ghost map.
//
implementation AbstractSanctum_create_page_table_mapping(ptbr: ppn_t, vaddr: vaddr_t, paddr: paddr_t, acl: pte_acl_t)
    returns (success : bool)
{
    var vpn: vpn_t;
    var ppn: ppn_t;

    vpn := vaddr2vpn(vaddr);
    ppn := paddr2ppn(paddr);

    ptbl_addr_map[ptbr, vpn]  := ppn;
    ptbl_acl_map[ptbr, vpn] := acl;

    success := true;
}
