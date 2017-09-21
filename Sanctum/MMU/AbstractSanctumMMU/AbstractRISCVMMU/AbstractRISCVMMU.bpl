
//
// Abstract translate (easy peasy).
//
procedure AbstractRISCV_translate(ptbr: ppn_t, access: riscv_access_t, vaddr: vaddr_t)
    returns (valid: bool, paddr: paddr_t, acl: pte_acl_t);
    ensures (valid == valid_translation(ptbl_acl_map, ptbr, access, vaddr));
    ensures (valid ==> acl2valid(acl));
    ensures (valid ==> (paddr == translate_vaddr2paddr(ptbl_addr_map, ptbr, vaddr)));
    ensures (valid ==> (acl == ptbl_acl_map[ptbr, vaddr2vpn(vaddr)]));
    ensures (valid && access == riscv_access_read) ==> acl2read(ptbl_acl_map[ptbr, vaddr2vpn(vaddr)]);
    ensures (valid && access == riscv_access_write) ==> acl2write(ptbl_acl_map[ptbr, vaddr2vpn(vaddr)]);
    ensures (valid && access == riscv_access_fetch) ==> acl2exec(ptbl_acl_map[ptbr, vaddr2vpn(vaddr)]);
