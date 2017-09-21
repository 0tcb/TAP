// ----------------------------------------------------------------- //
// Private Functions
// ----------------------------------------------------------------- //

/*
procedure sapi_load_page_table(ptbr: ppn_t, vaddr: vaddr_t, paddr: paddr_t, acl: pte_acl_t, level: int)
    returns (pte: word_t, ptbr_new: ppn_t);
    // globals.
    modifies mem;
    // preconditions.
    requires (level >= 0 && level <= 2);
    // Second-level table can't point back to the root.
    requires (forall i : vpn1_t ::
                bv2bool(pte2valid(load_pte1(mem, ptbr, i))) ==>
                    pte2ppn(load_pte1(mem, ptbr, i)) != ptbr);
    requires (level == 0 ==> bv2bool(pte2valid(load_pte1(mem, ptbr, vaddr2vpn1(vaddr)))));
    // postconditions for ptbr
    ensures ((level == 2) ==> ptbr_new == paddr2ppn(paddr));
    ensures ((level == 2) ==> (mem == old(mem)));
    // postconditions for the first level
    ensures ((level == 1) ==> (ptbr_new == ptbr));
    ensures ((level == 1) ==>
                (load_pte1(mem, ptbr_new, vaddr2vpn1(vaddr)) ==
                 pte_from_ppn_acl(paddr2ppn(paddr), acl)));
    ensures (forall i: vpn1_t::
                (level == 1 && i != vaddr2vpn1(vaddr)) ==>
                    (load_pte1(mem, ptbr_new, i) == load_pte1(old(mem), ptbr_new, i)));
    ensures (forall pa: wap_addr_t ::
              (level == 1 && pa != paddr2wpaddr(vpn1_to_pteaddr(ptbr_new, vaddr2vpn1(vaddr)))) ==>
              (mem[pa] == old(mem)[pa]));

    // postconditions for the second level
    ensures ((level == 0) ==> (ptbr_new == ptbr));
    ensures (forall pa: wap_addr_t ::
              (level == 0 && wpaddr2paddr(pa) !=
                             vpn0_to_pteaddr(pte2ppn(load_pte1(mem, ptbr_new, vaddr2vpn1(vaddr))),
                                             vaddr2vpn0(vaddr))) ==>
              (mem[pa] == old(mem)[pa]));
    ensures ((level == 0) ==> (load_pte0(mem,
                                         pte2ppn(load_pte1(mem, ptbr_new, vaddr2vpn1(vaddr))),
                                         vaddr2vpn0(vaddr)) ==
                               pte_from_ppn_acl(paddr2ppn(paddr), acl)));

    ensures (forall pa: wap_addr_t ::
                (level == 0) ==>  wpaddr2ppn(pa) == ptbr_new ==> mem[pa] == old(mem)[pa]);
    // postconditions for levels 1 and 0.
    ensures ((level == 0 || level == 1) ==> (pte == pte_from_ppn_acl(paddr2ppn(paddr), acl)));
    // postconditions for all levels
    ensures (forall i : vpn1_t ::
                ((level == 0 || level == 1) &&
                 paddr2ppn(paddr) != ptbr_new &&
                 bv2bool(pte2valid(load_pte1(mem, ptbr_new, i)))) ==>
                    pte2ppn(load_pte1(mem, ptbr_new, i)) != ptbr_new);
{
    var pte_addr: paddr_t;

    if (level == 2) {
        ptbr_new := paddr2ppn(paddr);
    } else if (level == 1) {
        ptbr_new := ptbr;

        pte_addr := vpn1_to_pteaddr(ptbr, vaddr2vpn1(vaddr));
        pte := pte_from_ppn_acl(paddr2ppn(paddr), acl);
        assert (paddr2ppn(paddr) != ptbr ==> pte2ppn(pte) != ptbr);
        call mem := STORE_LE_32(mem, pte_addr, pte);
        assert ptbr == old(ptbr);
        assert (forall pa: wap_addr_t ::
                    wpaddr2ppn(pa) != ptbr ==>
                        mem[pa] == old(mem)[pa]);
        assert (forall i : vpn1_t ::
                    (if (i == vaddr2vpn1(vaddr))
                        then load_pte1(mem, ptbr, i) == pte
                        else load_pte1(mem, ptbr, i) == load_pte1(old(mem), ptbr, i)));
        assert (forall i : vpn1_t ::
                    (paddr2ppn(paddr) != ptbr &&
                     bv2bool(pte2valid(load_pte1(mem, ptbr, i)))) ==>
                        pte2ppn(load_pte1(mem, ptbr, i)) != ptbr);
    } else if (level == 0) {
        ptbr_new := ptbr;

        pte_addr := vpn0_to_pteaddr(
                        pte2ppn(load_pte1(mem, ptbr, vaddr2vpn1(vaddr))),
                                vaddr2vpn0(vaddr));
        pte := pte_from_ppn_acl(paddr2ppn(paddr), acl);
        call mem := STORE_LE_32(mem, pte_addr, pte);
        assert (forall pa: wap_addr_t ::
                    wpaddr2ppn(pa) == ptbr ==>
                        mem[pa] == old(mem)[pa]);
        assert (forall i : vpn1_t ::
                    load_pte1(mem, ptbr, i) == load_pte1(old(mem), ptbr, i));
        assert (forall i : vpn1_t ::
                    ((level == 0 || level == 1) &&
                     paddr2ppn(paddr) != ptbr &&
                     bv2bool(pte2valid(load_pte1(mem, ptbr, i)))) ==>
                        pte2ppn(load_pte1(mem, ptbr, i)) != ptbr);
    }
}
*/

// ----------------------------------------------------------------- //
// Public Functions
// ----------------------------------------------------------------- //

implementation ConcreteSanctum_translate(
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

    call t_valid, paddr, acl := ConcreteRISCV_translate(t_ptbr, access, vaddr);
    valid_bmap := read_bitmap(t_drbmap, dram_region_for(paddr)) == 1bv1;
    not_in_pa_range  := AND_pa(paddr,t_parmask) != t_parbase;
    supervisor := cpu_mode == RISCV_MODE_S;
    valid := t_valid && acl_valid(acl, access, supervisor, cpu_mode_pum, cpu_mode_mxr) && valid_bmap && not_in_pa_range;
}

implementation ConcreteSanctum_create_page_table_mapping
    (ptbr: ppn_t, used_page_map: used_page_map_t, vaddr: vaddr_t, paddr: paddr_t, acl: pte_acl_t)
    returns (success: bool, used_page_map_new: used_page_map_t)
{
    // Variable to hold ptbr' returned by sapi_load_page_table.
    var ptbrp: ppn_t;

    // virtual address parts.
    var vpn1: vpn1_t;
    var vpn0: vpn0_t;
    // PPN.
    var ppn: ppn_t;

    // newly allocated page.
    var pg_avail: bool;
    var new_ppn: ppn_t;

    // page table entry addresses.
    var pte_addr1: paddr_t;
    var pte_addr0: paddr_t;

    // page table entries.
    var pte1: word_t;
    var pte0: word_t;

    // temporary copy of memory.
    var memp: mem_t;

    // is the valid bit in the acl set?
    var valid: bool;


    // Find the location of the first-level page table entry.
    vpn1 := vaddr2vpn1(vaddr);
    pte1 := load_pte1(mem, ptbr, vpn1);
    used_page_map_new := used_page_map;

    // Is this page table entry invalid?
    if (!bv2bool(pte2valid(pte1))) {
        // Allocate new page.
        call pg_avail, new_ppn, used_page_map_new := alloc_page(used_page_map);
        if (pg_avail) {
            // We need to make sure this page does not alias PTBR
            // zero it out.
            call zero_page(new_ppn);
            assert used_page_map_new[new_ppn];
            assert (forall p : ppn_t :: p != new_ppn ==> used_page_map_new[p] == used_page_map[p]);
            assert (forall wp: wap_addr_t ::
                        (wpaddr2ppn(wp) != new_ppn) ==> (mem[wp] == old(mem)[wp]));
            assert (forall wp: wap_addr_t ::
                        (wpaddr2ppn(wp) == ptbr) ==> (mem[wp] == old(mem)[wp]));
            assert (forall i : vpn1_t ::
                        load_pte1(mem, ptbr, i) == load_pte1(old(mem), ptbr, i));
            pte_addr1 := vpn1_to_pteaddr(ptbr, vaddr2vpn1(vaddr));
            pte1 := pte_from_ppn_acl(new_ppn, k_pg_valid_acl);
            call mem := STORE_LE_32(mem, pte_addr1, pte1);
            assert (pte2valid(load_pte1(mem, ptbr, vaddr2vpn1(vaddr))) == 1bv1);
        } else {
            success := false;
            return;
        }
    } else {
        assert (forall i : vpn1_t ::
                    bv2bool(pte2valid(load_pte1(mem, ptbr, i))) <==>
                    bv2bool(pte2valid(load_pte1(old(mem), ptbr, i))));
    }

    memp := mem;
    assert (forall i : vpn1_t ::
                bv2bool(pte2valid(load_pte1(mem, ptbr, i))) ==>
                    pte2ppn(load_pte1(mem, ptbr, i)) != ptbr);
    assert (load_pte1(mem, ptbr, vaddr2vpn1(vaddr)) == pte1);
    pte_addr0 := vpn0_to_pteaddr(pte2ppn(pte1), vaddr2vpn0(vaddr));
    pte0 := pte_from_ppn_acl(paddr2ppn(paddr), acl);
    call mem := STORE_LE_32(mem, pte_addr0, pte0);
    success := true;

    assert (bv2bool(pte2valid(load_pte1(mem, ptbr, vaddr2vpn1(vaddr)))));
    assert (load_pte0(mem, pte2ppn(pte1), vaddr2vpn0(vaddr)) == pte0);
    // Read the second-level, return its valid.
    assert (is_mapping_valid(mem, ptbr, vaddr) == acl2valid(acl));

    assert (forall pa: wap_addr_t :: wpaddr2ppn(pa) == ptbr ==> mem[pa] == memp[pa]);
    assert (forall i : vpn1_t ::
                load_pte1(mem, ptbr, i) == load_pte1(memp, ptbr, i));
    assert (pte2valid(load_pte1(mem, ptbr, vaddr2vpn1(vaddr))) == 1bv1);
}
