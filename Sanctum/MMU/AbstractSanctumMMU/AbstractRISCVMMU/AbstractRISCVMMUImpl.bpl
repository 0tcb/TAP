// ----------------------------------------------------------------- //
// Implementation of AbstractRISCVMMU
// ----------------------------------------------------------------- //

//
// Abstract translate (easy peasy).
//
implementation AbstractRISCV_translate(ptbr: ppn_t, access : riscv_access_t, vaddr: vaddr_t)
    returns (valid: bool, paddr: paddr_t, acl: pte_acl_t)
{
    var vpn: vpn_t;
    var ppn: ppn_t;
    vpn := vaddr2vpn(vaddr);
    paddr := ptbl_addr_map[ptbr, vpn] ++ vaddr2offset(vaddr);
    acl := ptbl_acl_map[ptbr, vpn];
    if (access == riscv_access_read) {
        valid := acl2valid(acl) && acl2read(acl);
    } else if (access == riscv_access_write) {
        valid := acl2valid(acl) && acl2write(acl);
    } else if (access == riscv_access_fetch) {
        valid := acl2valid(acl) && acl2exec(acl);
    } else {
        assert !valid_access(access);
        valid := false;
    }
}
