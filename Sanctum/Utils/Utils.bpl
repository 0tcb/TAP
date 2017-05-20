// ----------------------------------------------------------------- //
// Functions to allocate and deallocate pages.
// ----------------------------------------------------------------- //
//
// Allocate a page.
//
procedure alloc_page(used_page_map: used_page_map_t)
    returns (avail : bool, ppn: ppn_t, used_page_map_new: used_page_map_t);
    // used_page_map is updated.
    ensures (avail ==> used_page_map_new[ppn]);
    // We didn't give away a used page.
    ensures (avail ==> !used_page_map[ppn]);
    //must be within dram
    ensures (avail ==> is_dram_address(ppn2paddr(ppn)));
    // We didn't mess with other used_page_map entries.
    ensures (forall p : ppn_t ::
                (avail && p != ppn) ==> used_page_map_new[p] == used_page_map[p]);
    // We didn't mess with used_page_map at all if we failed (didn't allocate anything).
    ensures (forall p : ppn_t ::
             !avail ==> used_page_map_new[p] == used_page_map[p]);

//
// Allocate a page.
//
procedure alloc_page_from_region(used_page_map: used_page_map_t, region: region_t)
    returns (avail : bool, ppn: ppn_t, used_page_map_new: used_page_map_t);
    // used_page_map is updated.
    ensures (avail ==> used_page_map_new[ppn]);
    // We didn't give away a used page.
    ensures (avail ==> !used_page_map[ppn]);
    // We return a page in the correct region.
    ensures (avail ==> dram_region_for(ppn2paddr(ppn)) == region);
    //must be within dram
    ensures (avail ==> is_dram_address(ppn2paddr(ppn)));
    // We didn't mess with other used_page_map entries.
    ensures (forall p : ppn_t ::
                (avail && p != ppn) ==> used_page_map_new[p] == used_page_map[p]);
    // We didn't mess with used_page_map at all if we failed (didn't allocate anything).
    ensures (forall p : ppn_t ::
             !avail ==> used_page_map_new[p] == used_page_map[p]);

//
// Zero out a page.
//
procedure zero_page(ppn: ppn_t);
    modifies mem;
    ensures (forall pa : wap_addr_t ::
                if (wpaddr2ppn(pa) == ppn)
                    then mem[pa] == 0bv32
                    else mem[pa] == old(mem)[pa]);

//
// Deallocate a page.
//
procedure dealloc_page(used_page_map: used_page_map_t, ppn: ppn_t)
    returns (used_page_map_new: used_page_map_t);
    requires used_page_map[ppn];
    ensures !used_page_map_new[ppn];
    ensures (forall p: ppn_t :: p != ppn ==> used_page_map_new[p] == used_page_map[p]);
