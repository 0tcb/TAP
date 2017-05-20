
// ----------------------------------------------------------------- //
// Implementation of Public Functions
// ----------------------------------------------------------------- //

implementation ConcreteRISCV_translate(ptbr: ppn_t, vaddr: vaddr_t)
    returns (valid: bool, paddr: paddr_t, acl: pte_acl_t)
{
    var pte1, pte0: word_t;
    var ppn1, ppn: ppn_t;
    var vpn1: vpn1_t;
    var vpn0: vpn0_t;

    // compute the two parts of the VPN.
    vpn1 := vaddr2vpn1(vaddr);
    vpn0 := vaddr2vpn0(vaddr);

    // traverse the first level.
    pte1 := load_pte1(mem, ptbr, vpn1);
    ppn1 := pte2ppn(pte1);
    acl := pte2acl(pte1);
    valid := acl2valid(acl);
    if (!valid) { return; }

    // now for the second level.
    pte0 := load_pte0(mem, ppn1, vpn0);
    ppn := pte2ppn(pte0);
    acl := pte2acl(pte0);
    valid := acl2valid(acl);
    if (!valid) { return; }

    paddr := ppn ++ vaddr2offset(vaddr);
}
