// ----------------------------------------------------------------- //
// Implementation of AbstractRISCVMMU
// ----------------------------------------------------------------- //

//
// Abstract translate (easy peasy).
//
implementation AbstractRISCV_translate(ptbr: ppn_t, vaddr: vaddr_t)
    returns (valid: bool, paddr: paddr_t, acl: pte_acl_t)
{
    var vpn: vpn_t;
    var ppn: ppn_t;
    vpn := vaddr2vpn(vaddr);
    paddr := ptbl_addr_map[ptbr, vpn] ++ vaddr2offset(vaddr);
    acl := ptbl_acl_map[ptbr, vpn];
    valid := acl2valid(acl);
}
