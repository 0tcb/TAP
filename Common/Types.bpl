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
type cache_set_index_t = int;
type cache_way_index_t = int;
type cache_tag_t       = int; 

const kmax_cache_set_index_t : cache_set_index_t;
const kmax_cache_way_index_t : cache_way_index_t;
axiom kmax_cache_set_index_t > 0;
axiom kmax_cache_way_index_t > 0;

function {:inline} valid_cache_set_index(i : cache_set_index_t) : bool { i >= 0 && i < kmax_cache_set_index_t }
function {:inline} valid_cache_way_index(i : cache_way_index_t) : bool { i >= 0 && i < kmax_cache_way_index_t }

type cache_valid_map_t = [cache_set_index_t, cache_way_index_t]bool;
type cache_tag_map_t   = [cache_set_index_t, cache_way_index_t]cache_tag_t;

function paddr2set(pa : wap_addr_t) : cache_set_index_t;
function paddr2tag(pa : wap_addr_t) : cache_tag_t;

//--------------------------------------------------------------------------//
// Measurement                                                              //
//--------------------------------------------------------------------------//
type measurement_t = int;
const k0_measurement_t : measurement_t;
axiom k0_measurement_t == 0;

//--------------------------------------------------------------------------//
// utility fns                                                              //
//--------------------------------------------------------------------------//
function word2int(w : word_t) : int;
axiom (forall w1, w2 : word_t :: (w1 != w2) ==> (word2int(w1) != word2int(w2)));
axiom (forall w : word_t :: word2int(w) >= 0 && word2int(w) <= kmax_word_t_as_int);

function vaddr2int(va : vaddr_t) : int;
axiom (forall v1, v2 : vaddr_t :: (v1 != v2) ==> (vaddr2int(v1) != vaddr2int(v2)));
axiom (forall w : vaddr_t :: vaddr2int(w) >= 0 && vaddr2int(w) <= kmax_vaddr_t_as_int);

