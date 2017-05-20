implementation alloc_page(used_page_map: used_page_map_t)
    returns (avail : bool, ppn: ppn_t, used_page_map_new: used_page_map_t)
{
    var i: ppn_t;
    i := k0_ppn_t;
    avail := false;
    used_page_map_new := used_page_map;


    while (LT_ppn(i, num_dram_pages))
        invariant LE_ppn(i, num_dram_pages);
        invariant (forall p : ppn_t ::
                      (!avail && LT_ppn(p, i)) ==>
                        used_page_map[p] == old(used_page_map[p]));
    {
        if (!used_page_map[i]) {
            used_page_map_new[i] := true;
            avail := true;
            ppn := i;
            return;
        }
        i := PLUS_ppn(i, k1_ppn_t);
    }
}

implementation alloc_page_from_region(used_page_map: used_page_map_t, region: region_t)
    returns (avail : bool, ppn: ppn_t, used_page_map_new: used_page_map_t)
{
    var i: ppn_t;
    i := k0_ppn_t;
    avail := false;
    used_page_map_new := used_page_map;


    while (LT_ppn(i, num_dram_pages))
        invariant LE_ppn(i, num_dram_pages);
        invariant (forall p : ppn_t ::
                      (!avail && LT_ppn(p, i)) ==>
                        used_page_map[p] == old(used_page_map[p]));
    {
        if (!used_page_map[i] && region == dram_region_for(ppn2paddr(i))) {
            used_page_map_new[i] := true;
            avail := true;
            ppn := i;
            return;
        }
        i := PLUS_ppn(i, k1_ppn_t);
    }
}

implementation zero_page(ppn: ppn_t)
{
    var i: wpoffset1ex_t;
    i := k0_wpoffset1ex_t;

    while (LE_11(i, k1024_wpoffset1ex_t))
        invariant (forall pa : wap_addr_t ::
                    if (wpaddr2ppn(pa) == ppn && LT_11(0bv1++wpaddr2offset(pa), i))
                        then mem[pa] == k0_word_t
                        else mem[pa] == old(mem)[pa]);
    {
        mem := mem[(ppn ++ i[10:0]) := k0_word_t];
        i := PLUS_11(i, k1_wpoffset1ex_t);
    }
    assert (forall pa : wap_addr_t ::
                if (wpaddr2ppn(pa) == ppn)
                    then mem[pa] == k0_word_t
                    else mem[pa] == old(mem)[pa]);
}

implementation dealloc_page(used_page_map: used_page_map_t, ppn: ppn_t)
    returns (used_page_map_new: used_page_map_t)
{
    used_page_map_new := used_page_map;
    used_page_map_new[ppn] := false;
}
