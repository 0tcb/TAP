// -------------------------------------------------------------------- //
// address types.                                                       //
// -------------------------------------------------------------------- //
type vaddr_t = bv32;
type wap_addr_t = bv22;
type word_t  = bv32;

// -------------------------------------------------------------------- //
// constants and functions for vaddr_t                                  //
// -------------------------------------------------------------------- //
const kmax_vaddr_t : vaddr_t;
axiom kmax_vaddr_t == 4294967295bv32;
const kmax_vaddr_t_as_int : int;
axiom kmax_vaddr_t_as_int == 4294967295;
const k0_vaddr_t : vaddr_t;
axiom k0_vaddr_t == 0bv32;
const k1_vaddr_t : vaddr_t;
axiom k1_vaddr_t == 1bv32;
function {:bvbuiltin "bvshl"} LSHIFT_va(p1: vaddr_t, p2: vaddr_t) : vaddr_t;
function {:bvbuiltin "bvadd"} PLUS_va(p1: vaddr_t, p2: vaddr_t) : vaddr_t;
function {:bvbuiltin "bvsub"} MINUS_va(p1: vaddr_t, p2: vaddr_t) : vaddr_t;
function {:bvbuiltin "bvugt"} GT_va(p1: vaddr_t, p2: vaddr_t) : bool;
function {:bvbuiltin "bvuge"} GE_va(p1: vaddr_t, p2: vaddr_t) : bool;
function {:bvbuiltin "bvult"} LT_va(p1: vaddr_t, p2: vaddr_t) : bool;
function {:bvbuiltin "bvule"} LE_va(p1: vaddr_t, p2: vaddr_t) : bool;
function {:bvbuiltin "bvand"} AND_va(p1: vaddr_t, p2: vaddr_t) : vaddr_t;

// -------------------------------------------------------------------- //
// constants and functions for wap_addr_t                               //
// -------------------------------------------------------------------- //
const kmax_wap_addr_t : wap_addr_t;
axiom kmax_wap_addr_t == 4194303bv22;
const kmax_wap_addr_t_as_int : int;
axiom kmax_wap_addr_t_as_int == 4194303;
const k0_wap_addr_t : wap_addr_t;
axiom k0_wap_addr_t == 0bv22;
const k1_wap_addr_t : wap_addr_t;
axiom k1_wap_addr_t == 1bv22;
const k2_wap_addr_t : wap_addr_t;
axiom k2_wap_addr_t == 2bv22;

function {:bvbuiltin "bvadd"} PLUS_wapa(p1: wap_addr_t, p2: wap_addr_t) : wap_addr_t;
function {:bvbuiltin "bvsub"} MINUS_wapa(p1: wap_addr_t, p2: wap_addr_t) : wap_addr_t;
function {:bvbuiltin "bvult"} LT_wapa(p1: wap_addr_t, p2: wap_addr_t) : bool;
function {:bvbuiltin "bvule"} LE_wapa(p1: wap_addr_t, p2: wap_addr_t) : bool;
function {:bvbuiltin "bvugt"} GT_wapa(p1: wap_addr_t, p2: wap_addr_t) : bool;
function {:bvbuiltin "bvuge"} GE_wapa(p1: wap_addr_t, p2: wap_addr_t) : bool;

// -------------------------------------------------------------------- //
// memory.                                                              //
// -------------------------------------------------------------------- //
type mem_t = [wap_addr_t]word_t;

// -------------------------------------------------------------------- //
// constants and functions for word_t                                   //
// -------------------------------------------------------------------- //
const k0_word_t : word_t;
axiom k0_word_t == 0bv32;
const kmax_word_t : word_t;
axiom kmax_word_t == 4294967295bv32;
const kmax_word_t_as_int : int;
axiom kmax_word_t_as_int == 4294967295;

// -------------------------------------------------------------------- //
// uarch state                                                          //
// -------------------------------------------------------------------- //
type cache_set_index_t = bv9;
type cache_tag_t       = bv9; 
type cache_offset_t    = bv4; // 64B cache lines.
// 8 (tag) + 8 (set index) + 6 (offset) = 22 (size of wap_addr_t)
const k0_cache_set_index_t   : cache_set_index_t;
const k1_cache_set_index_t   : cache_set_index_t;
const kmax_cache_set_index_t : cache_set_index_t;
axiom k0_cache_set_index_t   == 0bv9;
axiom k1_cache_set_index_t   == 1bv9;
axiom kmax_cache_set_index_t == 511bv9;

type cache_valid_map_t = [cache_set_index_t]bool;
type cache_tag_map_t   = [cache_set_index_t]cache_tag_t;
function {:bvbuiltin "bvadd"} PLUS_csi(p1: cache_set_index_t, p2: cache_set_index_t) : cache_set_index_t;
function {:bvbuiltin "bvult"} LT_csi(p1: cache_set_index_t, p2: cache_set_index_t) : bool;

function paddr2set(pa : wap_addr_t) : cache_set_index_t;
function paddr2tag(pa : wap_addr_t) : cache_tag_t;

