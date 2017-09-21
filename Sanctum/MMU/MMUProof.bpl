// ----------------------------------------------------------------- //
// The equivalence proof.
// ----------------------------------------------------------------- //
function in_page_table_k(mem: mem_t, ptbr: ppn_t, ppn: ppn_t, k: vpn1_t): bool;
axiom (forall mem: mem_t, ptbr: ppn_t, ppn: ppn_t, k: vpn1_t ::
            (pte1valid(mem, ptbr, k) && pte2ppn(load_pte1(mem, ptbr, k)) == ppn) <==>
                in_page_table_k(mem, ptbr, ppn, k));
function in_page_table(mem: mem_t, ptbr: ppn_t, ppn: ppn_t): bool;
axiom (forall mem: mem_t, ptbr: ppn_t, ppn: ppn_t ::
            ((ptbr == ppn) ||
             (exists k: vpn1_t :: in_page_table_k(mem, ptbr, ppn, k))) <==>
             in_page_table(mem, ptbr, ppn));

procedure addr_for_havoc(ptbr: ppn_t)
    returns (wpaddr: wap_addr_t)
    ensures (!in_page_table(mem, ptbr, wpaddr2ppn(wpaddr)));
    ensures (forall k: vpn1_t ::
                pte1valid(mem, ptbr, k) ==>
                wpaddr2ppn(wpaddr) != pte2ppn(load_pte1(mem, ptbr, k)));
    ensures (wpaddr2ppn(wpaddr) != ptbr);
{
    var wppn: ppn_t;
    var v: vpn1ex_t;
    var pte: word_t;
    var ppn: ppn_t;
    var max: vpn1ex_t;
    var pgtbl: [ppn_t]bool;

    assume (forall p: ppn_t :: pgtbl[p] == false);

    // pgtbl[ppn] = true if ppn points to a part of the page table.
    pgtbl[ptbr] := true;
    v := k0_vpn1ex;
    max := PLUS_vpn1ex(0bv1++max_vpn1_t, k1_vpn1ex);
    while (LT_vpn1ex(v, max))
        invariant (pgtbl[ptbr]);
        invariant (mem == old(mem));
        invariant (forall vpn1: vpn1_t ::
                     LT_vpn1ex(0bv1++vpn1, v) ==>
                        (in_page_table_k(mem, ptbr, pte2ppn(load_pte1(mem, ptbr, vpn1)), vpn1) ==>
                            pgtbl[pte2ppn(load_pte1(mem, ptbr, vpn1))]));
        invariant (forall vpn1: vpn1_t ::
                     LT_vpn1ex(0bv1++vpn1, v) ==>
                        (bv2bool(pte2valid(load_pte1(mem, ptbr, vpn1))) ==>
                         pgtbl[pte2ppn(load_pte1(mem, ptbr, vpn1))]));
    {
        pte := load_pte1(mem, ptbr, vpn1ex_to_vpn1(v));
        ppn := pte2ppn(pte);
        if (bv2bool(pte2valid(pte))) {
            pgtbl[ppn] := true;
            assert in_page_table_k(mem, ptbr, ppn, vpn1ex_to_vpn1(v));
            assert pgtbl[ppn];
        }
        assert in_page_table_k(mem, ptbr, ppn, vpn1ex_to_vpn1(v)) ==> pgtbl[ppn];
        v := PLUS_vpn1ex(v, k1_vpn1ex);
    }
    assert in_page_table(mem, ptbr, ppn) ==> pgtbl[ppn];

    while (true) {
        havoc wpaddr;
        if (!in_page_table(mem, ptbr, wpaddr2ppn(wpaddr))) {
            assert (forall k: vpn1_t ::
                        pte1valid(mem, ptbr, k) ==>
                        wpaddr2ppn(wpaddr) != pte2ppn(load_pte1(mem, ptbr, k)));
            return;
        }
    }
}

//
// Havocs all parts of memory except the page tables.
//
procedure havoc_mem(ptbr: ppn_t)
    modifies mem;
    // --- postconditions --- //
    ensures (forall i : vpn1_t ::
                bv2bool(pte2valid(load_pte1(mem, ptbr, i))) ==
                    bv2bool(pte2valid(load_pte1(old(mem), ptbr, i))));
    ensures (forall vpn1 : vpn1_t, vpn0: vpn0_t ::
                bv2bool(pte2valid(load_pte1(mem, ptbr, vpn1))) ==>
                    load_pte0(mem, pte2ppn(load_pte1(mem, ptbr, vpn1)), vpn0) ==
                    load_pte0(old(mem), pte2ppn(load_pte1(old(mem), ptbr, vpn1)), vpn0));
    ensures (forall va: vaddr_t, access : riscv_access_t ::
                is_translation_valid(mem, ptbr, access, va) ==
                is_translation_valid(old(mem), ptbr, access, va));
    ensures (forall va: vaddr_t ::
                is_mapping_valid(mem, ptbr, va) ==>
                    (translate_vaddr2pte(mem, ptbr, va) ==
                     translate_vaddr2pte(old(mem), ptbr, va)));
    ensures (forall pa: wap_addr_t ::
                        (wpaddr2ppn(pa) == ptbr) ==>
                            mem[pa] == old(mem)[pa]);
    ensures (forall pa: wap_addr_t, vpn1: vpn1_t ::
                (bv2bool(pte2valid(load_pte1(mem, ptbr, vpn1))) &&
                 wpaddr2ppn(pa) == pte2ppn(load_pte1(mem, ptbr, vpn1))) ==>
                    mem[pa] == old(mem)[pa]);
{
    var wpaddr: wap_addr_t;
    var data: word_t;


    call wpaddr := addr_for_havoc(ptbr);
    assert !in_page_table(mem, ptbr, wpaddr2ppn(wpaddr));
    assert wpaddr2ppn(wpaddr) != ptbr;
    assert (forall vpn1: vpn1_t ::
                pte1valid(mem, ptbr, vpn1) ==>
                wpaddr2ppn(wpaddr) != pte2ppn(load_pte1(mem, ptbr, vpn1)));

    havoc data;
    call mem := STORE_WORD(mem, wpaddr, data);
    assert (forall pa: wap_addr_t ::
                pa != wpaddr ==> (mem[pa] == old(mem)[pa]));
    /*
    assert (forall pa: wap_addr_t ::
                in_page_table(mem, ptbr, wpaddr2ppn(pa)) ==>
                    mem[pa] == old(mem)[pa]);
    */
}

procedure proof()
    modifies mem, ptbl_addr_map, ptbl_acl_map;
{
    var ptbr : ppn_t;
    var pg_avail : bool;
    var used_page_map: used_page_map_t;

    var vaddr: vaddr_t;
    var paddr, paddr_spec, paddr_impl: paddr_t;
    var acl_spec, acl_impl: pte_acl_t;
    var acl: pte_acl_t;
    var v_spec, v_impl : bool;
    var vpn: vpn_t;
    var ppn: ppn_t;
    var access : riscv_access_t;

    var s1, s2, fail : bool;

    // initial all pages are available.
    assume (forall i : ppn_t :: !used_page_map[i]);

    // allocate the page table
    call pg_avail, ptbr, used_page_map := alloc_page(used_page_map);
    // No page? let's go home.
    if (!pg_avail) { return; }

    // invalidate the abstract page table.
    assume (forall v: vpn_t :: acl2valid(ptbl_acl_map[ptbr, v]) == false);

    // Zero out memory.
    assume (forall addr: wap_addr_t :: mem[addr] == k0_word_t);


    // A couple of sanity checks.
    assert (forall va : vaddr_t ::
            does_translation_exist(ptbl_acl_map, ptbr, va) == is_mapping_valid(mem, ptbr, va));

    // fail==true means alloc_page ran out of physical memory. All bets are off.
    fail := false;
    while (!fail)
        // Both abstract and implementation pages must be valid in the same way.
        invariant (forall va : vaddr_t ::
            !fail ==> does_translation_exist(ptbl_acl_map, ptbr, va) ==
                      is_mapping_valid(mem, ptbr, va));
        // And both must map to the same PPN.
        invariant (forall va : vaddr_t ::
            (!fail && does_translation_exist(ptbl_acl_map, ptbr, va) &&
                      is_mapping_valid(mem, ptbr, va)) ==>
                (ptbl_addr_map[ptbr, vaddr2vpn(va)] == translate_vaddr2ppn(mem, ptbr, va)));
        invariant (forall va : vaddr_t ::
            (!fail && does_translation_exist(ptbl_acl_map, ptbr, va) &&
                      is_mapping_valid(mem, ptbr, va)) ==>
                (ptbl_acl_map[ptbr, vaddr2vpn(va)] == translate_vaddr2acl(mem, ptbr, va)));
        // We don't muck with the PTBR.
        invariant (used_page_map[ptbr]);
        // Don't muck with page allocation map.
        invariant (forall i : vpn1_t ::
                bv2bool(pte2valid(load_pte1(mem, ptbr, i))) ==>
                    used_page_map[pte2ppn(load_pte1(mem, ptbr, i))]);
        // Don't muck with aliasing invariants.
        // Second-level tables don't alias with the top-level
        invariant (forall i : vpn1_t ::
                    bv2bool(pte2valid(load_pte1(mem, ptbr, i))) ==>
                        pte2ppn(load_pte1(mem, ptbr, i)) != ptbr);
        // Second-level tables don't alias among themselves.
        invariant (forall i : vpn1_t, j : vpn1_t ::
                    (i != j &&
                     bv2bool(pte2valid(load_pte1(mem, ptbr, i))) &&
                     bv2bool(pte2valid(load_pte1(mem, ptbr, j)))) ==>
                        pte2ppn(load_pte1(mem, ptbr, i)) !=
                        pte2ppn(load_pte1(mem, ptbr, j)));

    {
        havoc vaddr, paddr;
        havoc acl;
        havoc access;

        if (*) {
            call s1 := AbstractSanctum_create_page_table_mapping(ptbr, vaddr, paddr, acl);
            call s2, used_page_map :=
                    ConcreteSanctum_create_page_table_mapping(ptbr, used_page_map, vaddr, paddr, acl);
            if (!s1 || !s2) {
                fail := true;
            }
        } else if (*) {
            call havoc_mem(ptbr);
        } else {
            assert (!fail);
            call v_spec, paddr_spec, acl_spec := AbstractRISCV_translate(ptbr, access, vaddr);
            call v_impl, paddr_impl, acl_impl := ConcreteRISCV_translate(ptbr, access, vaddr);
            assert (v_spec == v_impl);
            assert (v_spec && v_impl) ==> (acl_spec == acl_impl);
            assert (v_spec && v_impl) ==> (paddr_spec == paddr_impl);
        }
    }
}

procedure translate.DeterminismCheck()
{
    var vaddr : vaddr_t;
    var cpu_mode : riscv_mode_t;
    var cpu_mode_pum, cpu_mode_mxr : bool;
    var valid, valid1 : bool;
    var b, b1, c, c1, d, d1 : bool;
    var mask, mask1, base, base1, paddr, paddr1 : paddr_t;
    var acl, acl1 : pte_acl_t;

    call valid, paddr, acl := translate(vaddr, riscv_access_read, cpu_mode, cpu_mode_pum, cpu_mode_mxr);
    call valid1, paddr1, acl1 := translate(vaddr, riscv_access_read, cpu_mode, cpu_mode_pum, cpu_mode_mxr);

    assert valid <==> valid1;
}
// ----------------------------------------------------------------- //
