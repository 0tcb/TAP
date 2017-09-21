
//
// "Real" translate -- walks the page table.
//
procedure ConcreteRISCV_translate(ptbr: ppn_t, access: riscv_access_t, vaddr: vaddr_t)
    returns (valid: bool, paddr: paddr_t, acl: pte_acl_t);
    ensures (valid == is_translation_valid(mem, ptbr, access, vaddr));
    ensures (valid ==> acl2valid(acl));
    ensures (valid && access == riscv_access_read) ==> acl2read(acl);
    ensures (valid && access == riscv_access_write) ==> acl2write(acl);
    ensures (valid && access == riscv_access_fetch) ==> acl2exec(acl);
    ensures (valid ==> paddr2ppn(paddr) == translate_vaddr2ppn(mem, ptbr, vaddr));
    ensures (valid ==> paddr2offset(paddr) == vaddr2offset(vaddr));
    ensures (valid ==> acl == translate_vaddr2acl(mem, ptbr, vaddr));
