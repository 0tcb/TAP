
//
// Abstract translate (easy peasy).
//
procedure AbstractRISCV_translate(ptbr: ppn_t, vaddr: vaddr_t)
    returns (valid: bool, paddr: paddr_t, acl: pte_acl_t);
    ensures (valid == does_translation_exist(ptbl_acl_map, ptbr, vaddr));
    ensures (valid == acl2valid(acl));
    ensures (valid ==> paddr == translate_vaddr2paddr(ptbl_addr_map, ptbr, vaddr));
    ensures (valid ==> acl == ptbl_acl_map[ptbr, vaddr2vpn(vaddr)]);
