// ----------------------------------------------------------------- //
// Utility functions to query the ghost page table.
// ----------------------------------------------------------------- //
function {:inline} does_translation_exist(ptbl_acl_map: ptbl_acl_map_t, ptbr: ppn_t, vaddr: vaddr_t): bool
{
    acl2valid(ptbl_acl_map[ptbr, vaddr2vpn(vaddr)])
}

function {:inline} valid_translation(ptbl_acl_map: ptbl_acl_map_t, ptbr: ppn_t, access: riscv_access_t, vaddr: vaddr_t): bool
{
    if (access == riscv_access_read) 
        then acl2valid(ptbl_acl_map[ptbr, vaddr2vpn(vaddr)]) && acl2read(ptbl_acl_map[ptbr, vaddr2vpn(vaddr)])
        else (if (access == riscv_access_write)
                 then acl2valid(ptbl_acl_map[ptbr, vaddr2vpn(vaddr)]) && acl2write(ptbl_acl_map[ptbr, vaddr2vpn(vaddr)])
                 else (if (access == riscv_access_fetch)
                        then acl2valid(ptbl_acl_map[ptbr, vaddr2vpn(vaddr)]) && acl2exec(ptbl_acl_map[ptbr, vaddr2vpn(vaddr)])
                        else false))
}

function {:inline} translate_vaddr2paddr(addr_map: ptbl_addr_map_t, ptbr: ppn_t, vaddr: vaddr_t): paddr_t
{
    addr_map[ptbr, vaddr2vpn(vaddr)] ++ vaddr2offset(vaddr)
}

// ----------------------------------------------------------------- //
// Utility functions to query the actual page table.
// ----------------------------------------------------------------- //
//
// Is this first-level page table entry valid?
//
function {:inline} pte1valid(mem: mem_t, base: ppn_t, vpn1: vpn1_t) : bool
{ bv2bool(load_pte1(mem, base, vpn1)[1:0]) }
//
// Are both levels of the page table valid?
//
function {:inline} is_mapping_valid(mem: mem_t, base: ppn_t, vaddr: vaddr_t ) : bool
{
    // TODO: check for permissions. Handle big pages.
    // Read the first-level, ensure its valid.
    bv2bool(pte2valid(load_pte1(mem, base, vaddr2vpn1(vaddr)))) &&
    // Read the second-level, return its valid.
    bv2bool(pte2valid(
                load_pte0(mem,
                          pte2ppn(load_pte1(mem, base, vaddr2vpn1(vaddr))),
                          vaddr2vpn0(vaddr))))
}
//
// Are both levels of the page table valid and are the permissions correct?
//
function {:inline} is_translation_valid(mem: mem_t, base: ppn_t, access : riscv_access_t, vaddr: vaddr_t ) : bool
{
    // TODO: check for permissions. Handle big pages.
    // Read the first-level, ensure its valid.
    bv2bool(pte2valid(load_pte1(mem, base, vaddr2vpn1(vaddr)))) &&
    // Read the second-level, return its valid.
    bv2bool(pte2valid(
                load_pte0(mem,
                          pte2ppn(load_pte1(mem, base, vaddr2vpn1(vaddr))),
                          vaddr2vpn0(vaddr)))) &&
    (if (access == riscv_access_read)
        then (acl2read(pte2acl(load_pte0(mem, pte2ppn(load_pte1(mem, base, vaddr2vpn1(vaddr))), vaddr2vpn0(vaddr)))))
        else (if (access == riscv_access_write) 
                 then (acl2write(pte2acl(load_pte0(mem, pte2ppn(load_pte1(mem, base, vaddr2vpn1(vaddr))), vaddr2vpn0(vaddr)))))
                 else (if (access == riscv_access_fetch)
                          then (acl2exec(pte2acl(load_pte0(mem, pte2ppn(load_pte1(mem, base, vaddr2vpn1(vaddr))), vaddr2vpn0(vaddr)))))
                          else false)))
}
//
// Function that traverses both levels of the PTE. Returns leaf. Use only when
// both levels are guaranteed to be valid.
//
function {:inline} translate_vaddr2pte(mem: mem_t, base: ppn_t, vaddr: vaddr_t ) : word_t
{
    load_pte0(mem,
              pte2ppn(load_pte1(mem,
                                base,
                                vaddr2vpn1(vaddr))),
              vaddr2vpn0(vaddr))
}
//
// Function that traverses both levels of the PTE. Returns PPN. Use only when
// both levels are guaranteed to be valid.
//
function {:inline} translate_vaddr2ppn(mem: mem_t, base: ppn_t, vaddr: vaddr_t ) : ppn_t
{
    pte2ppn(load_pte0(mem,
                      pte2ppn(load_pte1(mem,
                                        base,
                                        vaddr2vpn1(vaddr))),
                      vaddr2vpn0(vaddr)))
}
//
// Function that traverses both levels of the PTE. Returns ACL. Use only when
// both levels are guaranteed to be valid.
//
function {:inline} translate_vaddr2acl(mem: mem_t, base: ppn_t, vaddr: vaddr_t ) : pte_acl_t
{
    pte2acl(load_pte0(mem,
                      pte2ppn(load_pte1(mem,
                                        base,
                                        vaddr2vpn1(vaddr))),
                      vaddr2vpn0(vaddr)))
}

// ----------------------------------------------------------------- //
// Translation functions.
// ----------------------------------------------------------------- //

function {:inline} in_enclave_mem(vaddr: vaddr_t, evbase: vaddr_t, evmask: vaddr_t): bool
{ (AND_va(vaddr,evmask) == evbase) }

function {:inline} paddr_valid(
    paddr: paddr_t,
    t_ptbr: ppn_t,
    t_drbmap: bitmap_t,
    t_parbase: paddr_t,
    t_parmask: paddr_t
) : bool
{
    (read_bitmap(t_drbmap, dram_region_for(paddr)) == 1bv1) &&
    (AND_pa(paddr,t_parmask) != t_parbase)
}

function {:inline} acl_valid(
    acl             : pte_acl_t,
    access          : riscv_access_t,
    supervisor      : bool,
    cpu_mode_pum    : bool,
    cpu_mode_mxr    : bool
) : bool
{
    (acl2valid(acl))                                        &&
    (acl2user(acl) && supervisor ==> cpu_mode_pum)          &&
    (acl2write(acl) ==> acl2read(acl))                      &&
    (access == riscv_access_fetch ==> acl2exec(acl))        &&
    (access == riscv_access_read ==>
        (acl2read(acl) || (cpu_mode_mxr && acl2exec(acl)))) &&
    (access == riscv_access_write ==>
        (acl2read(acl) && acl2write(acl)))
}

function {:inline} select_ppn(eid: enclave_id_t,
                     vaddr: vaddr_t, cpu_evbase: vaddr_t, cpu_evmask: vaddr_t,
                     eppn: ppn_t, ppn: ppn_t) : ppn_t
{
    if (eid != null_enclave_id && in_enclave_mem(vaddr, cpu_evbase, cpu_evmask))
        then eppn
        else ppn
}

function {:inline} select_drbmap(eid: enclave_id_t,
                     vaddr: vaddr_t, evbase: vaddr_t, evmask: vaddr_t,
                     edrbmap: bitmap_t, drbmap: bitmap_t) : bitmap_t
{
    if (eid != null_enclave_id && in_enclave_mem(vaddr, evbase, evmask))
        then edrbmap
        else drbmap
}

function {:inline} select_paddr(eid: enclave_id_t,
                     vaddr: vaddr_t, evbase: vaddr_t, evmask: vaddr_t,
                     epaddr: paddr_t, paddr: paddr_t) : paddr_t
{
    if (eid != null_enclave_id && in_enclave_mem(vaddr, evbase, evmask))
        then epaddr
        else paddr
}
