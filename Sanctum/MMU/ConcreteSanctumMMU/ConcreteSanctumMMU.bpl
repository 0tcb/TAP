procedure ConcreteSanctum_translate(
    vaddr: vaddr_t,
    access: riscv_access_t,
    cpu_mode: riscv_mode_t,
    cpu_mode_pum: bool,
    cpu_mode_mxr: bool
)
    returns (valid: bool, paddr: paddr_t, acl: pte_acl_t);
    ensures (valid <==>
        (is_translation_valid(mem, select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), access, vaddr)) &&
        (acl_valid(acl, access, cpu_mode == RISCV_MODE_S, cpu_mode_pum, cpu_mode_mxr)) &&
        (read_bitmap(select_drbmap(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_edrbmap, cpu_drbmap), dram_region_for(paddr)) == 1bv1) &&
        (AND_pa(paddr, select_paddr(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eparmask, cpu_parmask)) != select_paddr(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eparbase, cpu_parbase)));
    ensures (valid ==> paddr2ppn(paddr) == translate_vaddr2ppn(mem, select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr));
    ensures (valid ==> paddr2offset(paddr) == vaddr2offset(vaddr));
    ensures (valid ==> acl == translate_vaddr2acl(mem, select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr));

procedure ConcreteSanctum_create_page_table_mapping(
    ptbr: ppn_t,
    used_page_map: used_page_map_t,
    vaddr: vaddr_t,
    paddr: paddr_t,
    acl: pte_acl_t
)

    returns (success: bool, used_page_map_new: used_page_map_t);
    // modifies
    modifies mem;

    //------------ preconditions ------------------------------------------- //

    // First-level page table must be allocated.
    requires (used_page_map[ptbr]);
    // Any valid second-level page tables must also be allocated.
    requires (forall i : vpn1_t ::
                bv2bool(pte2valid(load_pte1(mem, ptbr, i))) ==>
                    used_page_map[pte2ppn(load_pte1(mem, ptbr, i))]);
    // Can't alias one of the second-level page tables back to top-level table.
    requires (forall i : vpn1_t ::
                bv2bool(pte2valid(load_pte1(mem, ptbr, i))) ==>
                    pte2ppn(load_pte1(mem, ptbr, i)) != ptbr);
    // Second-level page tables can't alias each other. (It might be possible
    // to make this type of aliasing work, but the proofs will be a mess.)
    requires (forall i : vpn1_t, j : vpn1_t ::
                (i != j &&
                 bv2bool(pte2valid(load_pte1(mem, ptbr, i))) &&
                 bv2bool(pte2valid(load_pte1(mem, ptbr, j)))) ==>
                    pte2ppn(load_pte1(mem, ptbr, i)) !=
                    pte2ppn(load_pte1(mem, ptbr, j)));

    //------------ postconditions ------------------------------------------- //

    // If we succeed, the  first-level PTE is always valid.
    ensures (success ==> pte2valid(load_pte1(mem, ptbr, vaddr2vpn1(vaddr))) == 1bv1);
    // If we succeed, the valid bit is set appropriately
    ensures (success ==> is_mapping_valid(mem, ptbr, vaddr) == acl2valid(acl));
    // If we succeed, the PTE translates to the right PPN.
    ensures (success ==> translate_vaddr2ppn(mem, ptbr, vaddr) == paddr2ppn(paddr));
    // If we succeed, the PTE has the right ACL.
    ensures (success ==> translate_vaddr2acl(mem, ptbr, vaddr) == acl);
    // Regardless of whatever happens, other VPNs translate the same way as before.
    ensures (forall va: vaddr_t ::
                    (vaddr2vpn(va) != vaddr2vpn(vaddr)) ==>
                        (is_mapping_valid(mem, ptbr, va) <==>
                            is_mapping_valid(old(mem), ptbr, va)));
    ensures (forall va: vaddr_t ::
                    (vaddr2vpn(va) != vaddr2vpn(vaddr) &&
                        is_mapping_valid(mem, ptbr, va)) ==>
                         translate_vaddr2ppn(mem, ptbr, va) ==
                         translate_vaddr2ppn(old(mem), ptbr, va));
    ensures (forall va: vaddr_t ::
                    (vaddr2vpn(va) != vaddr2vpn(vaddr) &&
                        is_mapping_valid(mem, ptbr, va)) ==>
                         translate_vaddr2acl(mem, ptbr, va) ==
                         translate_vaddr2acl(old(mem), ptbr, va));
    // We maintain the used_page_map invariants.
    // First, on ptbr.
    ensures (used_page_map_new[ptbr]);
    // And also on the second-level page tables.
    ensures (forall i : vpn1_t ::
                bv2bool(pte2valid(load_pte1(mem, ptbr, i))) ==>
                    used_page_map_new[pte2ppn(load_pte1(mem, ptbr, i))]);
    // We maintain the aliasing invariant.
    ensures (forall i : vpn1_t ::
                bv2bool(pte2valid(load_pte1(mem, ptbr, i))) ==>
                    pte2ppn(load_pte1(mem, ptbr, i)) != ptbr);
    ensures (forall i : vpn1_t, j : vpn1_t ::
                (i != j &&
                 bv2bool(pte2valid(load_pte1(mem, ptbr, i))) &&
                 bv2bool(pte2valid(load_pte1(mem, ptbr, j)))) ==>
                    pte2ppn(load_pte1(mem, ptbr, i)) !=
                    pte2ppn(load_pte1(mem, ptbr, j)));
