// ----------------------------------------------------------------- //
// State variables.
// ----------------------------------------------------------------- //

var mem: mem_t;
var ptbl_addr_map: ptbl_addr_map_t; // What does this VPN map to? (Ghost)
var ptbl_acl_map: ptbl_acl_map_t; // What are the permissions, etc. associated with this vpn?

/**********************************
 * CPU State                      *
 **********************************/

var cpu_evbase                          : vaddr_t;
var cpu_evmask                          : vaddr_t;
var cpu_eptbr                           : ppn_t;
var cpu_ptbr                            : ppn_t;
var cpu_drbmap                          : bitmap_t; //TODO: this can never exceed 64 bits
var cpu_edrbmap                         : bitmap_t;
var cpu_parbase                         : paddr_t;
var cpu_parmask                         : paddr_t;
var cpu_eparbase                        : paddr_t;
var cpu_eparmask                        : paddr_t;
var cpu_dmarbase                        : paddr_t;
var cpu_dmarmask                        : paddr_t;
var core_info_enclave_id                : enclave_id_t;
var core_info_thread_id                 : thread_id_t;
var core_flushed_at                     : int;

// ----------------------------------------------------------------- //
// Public Functions
// ----------------------------------------------------------------- //

procedure create_page_table_mapping(ptbr: ppn_t, vaddr: vaddr_t, paddr: paddr_t, acl: pte_acl_t)
    returns (success : bool);
    modifies ptbl_addr_map, ptbl_acl_map;
    ensures ptbl_addr_map[ptbr, vaddr2vpn(vaddr)] == paddr2ppn(paddr);
    ensures ptbl_acl_map[ptbr, vaddr2vpn(vaddr)] == acl;
    ensures (forall va : vaddr_t ::
                vaddr2vpn(va) != vaddr2vpn(vaddr) ==>
                     ptbl_addr_map[ptbr, vaddr2vpn(va)] == old(ptbl_addr_map[ptbr, vaddr2vpn(va)]));
    ensures (forall va : vaddr_t ::
                vaddr2vpn(va) != vaddr2vpn(vaddr) ==>
                     ptbl_acl_map[ptbr, vaddr2vpn(va)] == old(ptbl_acl_map[ptbr, vaddr2vpn(va)]));


procedure translate(
    vaddr: vaddr_t,
    access: riscv_access_t,
    cpu_mode: riscv_mode_t,
    cpu_mode_pum: bool,
    cpu_mode_mxr: bool
)
    returns (valid: bool, paddr: paddr_t, acl: pte_acl_t);
    ensures (valid ==> does_translation_exist(ptbl_acl_map, select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr));
	ensures (valid && access == riscv_access_read) ==> 
				acl2read(ptbl_acl_map[select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(vaddr)]);
	ensures (valid && access == riscv_access_write) ==> 
				 acl2write(ptbl_acl_map[select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(vaddr)]);
	ensures (valid && access == riscv_access_fetch) ==> 
				 acl2exec(ptbl_acl_map[select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(vaddr)]);
    ensures (valid <==>
        ((acl_valid(ptbl_acl_map[select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(vaddr)], access, cpu_mode == RISCV_MODE_S, cpu_mode_pum, cpu_mode_mxr)) &&
		 (valid_translation(ptbl_acl_map, select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), access, vaddr)) &&
         (read_bitmap(select_drbmap(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_edrbmap, cpu_drbmap), dram_region_for(ptbl_addr_map[select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(vaddr)] ++ vaddr2offset(vaddr))) == 1bv1) &&
         (AND_pa(ptbl_addr_map[select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(vaddr)] ++ vaddr2offset(vaddr), select_paddr(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eparmask, cpu_parmask)) != select_paddr(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eparbase, cpu_parbase))));
    ensures (valid ==> (paddr == ptbl_addr_map[select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(vaddr)] ++ vaddr2offset(vaddr)));
    ensures (valid ==> (paddr == translate_vaddr2paddr(ptbl_addr_map, select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr)));
    ensures (valid ==> (acl == ptbl_acl_map[select_ppn(core_info_enclave_id, vaddr, cpu_evbase, cpu_evmask, cpu_eptbr, cpu_ptbr), vaddr2vpn(vaddr)]));

