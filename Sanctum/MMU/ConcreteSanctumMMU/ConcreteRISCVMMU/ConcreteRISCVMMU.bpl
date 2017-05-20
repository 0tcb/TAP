
//
// "Real" translate -- walks the page table.
//
procedure ConcreteRISCV_translate(ptbr: ppn_t, vaddr: vaddr_t)
    returns (valid: bool, paddr: paddr_t, acl: pte_acl_t);
    ensures (valid == is_translation_valid(mem, ptbr, vaddr));
    ensures (valid <==> acl2valid(acl));
    ensures (valid ==> paddr2ppn(paddr) == translate_vaddr2ppn(mem, ptbr, vaddr));
    ensures (valid ==> paddr2offset(paddr) == vaddr2offset(vaddr));
    ensures (valid ==> acl == translate_vaddr2acl(mem, ptbr, vaddr));
