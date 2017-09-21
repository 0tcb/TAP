

/* functions to simplify the encoding from Boogie to Z3
  NOTE: don't put machine specific things here
*/

/* Bitvector operations */
function {:bvbuiltin "bvand"} AND_1(p1: bv1, p2: bv1) : bv1;
function {:bvbuiltin "bvor"} OR_1(p1: bv1, p2: bv1) : bv1;
function {:bvbuiltin "bvxor"} XOR_1(p1: bv1, p2: bv1) : bv1;
function {:bvbuiltin "bvnot"} NOT_1(p1: bv1) : bv1;

function {:bvbuiltin "bvadd"} PLUS_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvsub"} MINUS_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvmul"} TIMES_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvmod"} MOD_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvsmod"} SMOD_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvshl"} LSHIFT_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvlshr"} RSHIFT_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvashr"} ARSHIFT_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvand"} AND_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvor"} OR_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvxor"} XOR_8(p1: bv8, p2: bv8) : bv8;
function {:bvbuiltin "bvult"} LT_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvule"} LE_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvugt"} GT_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvuge"} GE_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvslt"} SLT_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvsle"} SLE_8(p1: bv8, p2: bv8) : bool;
function {:bvbuiltin "bvneg"} NEG_8(p1: bv8) : bv8;
function {:bvbuiltin "bvnot"} NOT_8(p1: bv8) : bv8;

function {:bvbuiltin "bvadd"} PLUS_10(p1: bv10, p2: bv10) : bv10;
function {:bvbuiltin "bvsub"} MINUS_10(p1: bv10, p2: bv10) : bv10;
function {:bvbuiltin "bvmul"} TIMES_10(p1: bv10, p2: bv10) : bv10;
function {:bvbuiltin "bvmod"} MOD_10(p1: bv10, p2: bv10) : bv10;
function {:bvbuiltin "bvsmod"} SMOD_10(p1: bv10, p2: bv10) : bv10;
function {:bvbuiltin "bvshl"} LSHIFT_10(p1: bv10, p2: bv10) : bv10;
function {:bvbuiltin "bvlshr"} RSHIFT_10(p1: bv10, p2: bv10) : bv10;
function {:bvbuiltin "bvashr"} ARSHIFT_10(p1: bv10, p2: bv10) : bv10;
function {:bvbuiltin "bvand"} AND_10(p1: bv10, p2: bv10) : bv10;
function {:bvbuiltin "bvor"} OR_10(p1: bv10, p2: bv10) : bv10;
function {:bvbuiltin "bvxor"} XOR_10(p1: bv10, p2: bv10) : bv10;
function {:bvbuiltin "bvult"} LT_10(p1: bv10, p2: bv10) : bool;
function {:bvbuiltin "bvule"} LE_10(p1: bv10, p2: bv10) : bool;
function {:bvbuiltin "bvugt"} GT_10(p1: bv10, p2: bv10) : bool;
function {:bvbuiltin "bvuge"} GE_10(p1: bv10, p2: bv10) : bool;
function {:bvbuiltin "bvslt"} SLT_10(p1: bv10, p2: bv10) : bool;
function {:bvbuiltin "bvsle"} SLE_10(p1: bv10, p2: bv10) : bool;
function {:bvbuiltin "bvneg"} NEG_10(p1: bv10) : bv10;
function {:bvbuiltin "bvnot"} NOT_10(p1: bv10) : bv10;

function {:bvbuiltin "bvadd"} PLUS_11(p1: bv11, p2: bv11) : bv11;
function {:bvbuiltin "bvsub"} MINUS_11(p1: bv11, p2: bv11) : bv11;
function {:bvbuiltin "bvmul"} TIMES_11(p1: bv11, p2: bv11) : bv11;
function {:bvbuiltin "bvmod"} MOD_11(p1: bv11, p2: bv11) : bv11;
function {:bvbuiltin "bvsmod"} SMOD_11(p1: bv11, p2: bv11) : bv11;
function {:bvbuiltin "bvshl"} LSHIFT_11(p1: bv11, p2: bv11) : bv11;
function {:bvbuiltin "bvlshr"} RSHIFT_11(p1: bv11, p2: bv11) : bv11;
function {:bvbuiltin "bvashr"} ARSHIFT_11(p1: bv11, p2: bv11) : bv11;
function {:bvbuiltin "bvand"} AND_11(p1: bv11, p2: bv11) : bv11;
function {:bvbuiltin "bvor"} OR_11(p1: bv11, p2: bv11) : bv11;
function {:bvbuiltin "bvxor"} XOR_11(p1: bv11, p2: bv11) : bv11;
function {:bvbuiltin "bvult"} LT_11(p1: bv11, p2: bv11) : bool;
function {:bvbuiltin "bvule"} LE_11(p1: bv11, p2: bv11) : bool;
function {:bvbuiltin "bvugt"} GT_11(p1: bv11, p2: bv11) : bool;
function {:bvbuiltin "bvuge"} GE_11(p1: bv11, p2: bv11) : bool;
function {:bvbuiltin "bvslt"} SLT_11(p1: bv11, p2: bv11) : bool;
function {:bvbuiltin "bvsle"} SLE_11(p1: bv11, p2: bv11) : bool;
function {:bvbuiltin "bvneg"} NEG_11(p1: bv11) : bv11;
function {:bvbuiltin "bvnot"} NOT_11(p1: bv11) : bv11;

function {:bvbuiltin "bvadd"} PLUS_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvsub"} MINUS_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvmul"} TIMES_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvmod"} MOD_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvsmod"} SMOD_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvshl"} LSHIFT_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvlshr"} RSHIFT_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvashr"} ARSHIFT_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvand"} AND_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvor"} OR_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvxor"} XOR_16(p1: bv16, p2: bv16) : bv16;
function {:bvbuiltin "bvult"} LT_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvule"} LE_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvugt"} GT_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvuge"} GE_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvslt"} SLT_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvsle"} SLE_16(p1: bv16, p2: bv16) : bool;
function {:bvbuiltin "bvneg"} NEG_16(p1: bv16) : bv16;
function {:bvbuiltin "bvnot"} NOT_16(p1: bv16) : bv16;

function {:bvbuiltin "bvadd"} PLUS_20(p1: bv20, p2: bv20) : bv20;
function {:bvbuiltin "bvsub"} MINUS_20(p1: bv20, p2: bv20) : bv20;
function {:bvbuiltin "bvmul"} TIMES_20(p1: bv20, p2: bv20) : bv20;
function {:bvbuiltin "bvmod"} MOD_20(p1: bv20, p2: bv20) : bv20;
function {:bvbuiltin "bvsmod"} SMOD_20(p1: bv20, p2: bv20) : bv20;
function {:bvbuiltin "bvshl"} LSHIFT_20(p1: bv20, p2: bv20) : bv20;
function {:bvbuiltin "bvlshr"} RSHIFT_20(p1: bv20, p2: bv20) : bv20;
function {:bvbuiltin "bvashr"} ARSHIFT_20(p1: bv20, p2: bv20) : bv20;
function {:bvbuiltin "bvand"} AND_20(p1: bv20, p2: bv20) : bv20;
function {:bvbuiltin "bvor"} OR_20(p1: bv20, p2: bv20) : bv20;
function {:bvbuiltin "bvxor"} XOR_20(p1: bv20, p2: bv20) : bv20;
function {:bvbuiltin "bvult"} LT_20(p1: bv20, p2: bv20) : bool;
function {:bvbuiltin "bvule"} LE_20(p1: bv20, p2: bv20) : bool;
function {:bvbuiltin "bvugt"} GT_20(p1: bv20, p2: bv20) : bool;
function {:bvbuiltin "bvuge"} GE_20(p1: bv20, p2: bv20) : bool;
function {:bvbuiltin "bvslt"} SLT_20(p1: bv20, p2: bv20) : bool;
function {:bvbuiltin "bvsle"} SLE_20(p1: bv20, p2: bv20) : bool;
function {:bvbuiltin "bvneg"} NEG_20(p1: bv20) : bv20;
function {:bvbuiltin "bvnot"} NOT_20(p1: bv20) : bv20;

function {:bvbuiltin "bvadd"} PLUS_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvsub"} MINUS_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvmul"} TIMES_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvmod"} MOD_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvsmod"} SMOD_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvshl"} LSHIFT_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvlshr"} RSHIFT_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvashr"} ARSHIFT_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvand"} AND_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvor"} OR_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvxor"} XOR_32(p1: bv32, p2: bv32) : bv32;
function {:bvbuiltin "bvult"} LT_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvule"} LE_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvugt"} GT_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvuge"} GE_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvslt"} SLT_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvsle"} SLE_32(p1: bv32, p2: bv32) : bool;
function {:bvbuiltin "bvneg"} NEG_32(p1: bv32) : bv32;
function {:bvbuiltin "bvnot"} NOT_32(p1: bv32) : bv32;

function {:bvbuiltin "bvadd"} PLUS_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvsub"} MINUS_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvmul"} TIMES_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvmod"} MOD_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvsmod"} SMOD_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvshl"} LSHIFT_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvlshr"} RSHIFT_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvashr"} ARSHIFT_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvand"} AND_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvor"} OR_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvxor"} XOR_64(p1: bv64, p2: bv64) : bv64;
function {:bvbuiltin "bvult"} LT_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvule"} LE_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvugt"} GT_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvuge"} GE_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvslt"} SLT_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvsle"} SLE_64(p1: bv64, p2: bv64) : bool;
function {:bvbuiltin "bvneg"} NEG_64(p1: bv64) : bv64;
function {:bvbuiltin "bvnot"} NOT_64(p1: bv64) : bv64;

function {:bvbuiltin "bvadd"} PLUS_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : wap1ex_addr_t;
function {:bvbuiltin "bvsub"} MINUS_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : wap1ex_addr_t;
function {:bvbuiltin "bvmul"} TIMES_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : wap1ex_addr_t;
function {:bvbuiltin "bvmod"} MOD_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : wap1ex_addr_t;
function {:bvbuiltin "bvsmod"} SMOD_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : wap1ex_addr_t;
function {:bvbuiltin "bvshl"} LSHIFT_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : wap1ex_addr_t;
function {:bvbuiltin "bvlshr"} RSHIFT_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : wap1ex_addr_t;
function {:bvbuiltin "bvashr"} ARSHIFT_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : wap1ex_addr_t;
function {:bvbuiltin "bvand"} AND_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : wap1ex_addr_t;
function {:bvbuiltin "bvor"} OR_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : wap1ex_addr_t;
function {:bvbuiltin "bvxor"} XOR_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : wap1ex_addr_t;
function {:bvbuiltin "bvult"} LT_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : bool;
function {:bvbuiltin "bvule"} LE_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : bool;
function {:bvbuiltin "bvugt"} GT_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : bool;
function {:bvbuiltin "bvuge"} GE_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : bool;
function {:bvbuiltin "bvslt"} SLT_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : bool;
function {:bvbuiltin "bvsle"} SLE_wap1ex(p1: wap1ex_addr_t, p2: wap1ex_addr_t) : bool;
function {:bvbuiltin "bvneg"} NEG_wap1ex(p1: wap1ex_addr_t) : wap1ex_addr_t;
function {:bvbuiltin "bvnot"} NOT_wap1ex(p1: wap1ex_addr_t) : wap1ex_addr_t;

function {:bvbuiltin "bvadd"} PLUS_pa(p1: paddr_t, p2: paddr_t) : paddr_t;
function {:bvbuiltin "bvsub"} MINUS_pa(p1: paddr_t, p2: paddr_t) : paddr_t;
function {:bvbuiltin "bvmul"} TIMES_pa(p1: paddr_t, p2: paddr_t) : paddr_t;
function {:bvbuiltin "bvmod"} MOD_pa(p1: paddr_t, p2: paddr_t) : paddr_t;
function {:bvbuiltin "bvsmod"} SMOD_pa(p1: paddr_t, p2: paddr_t) : paddr_t;
function {:bvbuiltin "bvshl"} LSHIFT_pa(p1: paddr_t, p2: paddr_t) : paddr_t;
function {:bvbuiltin "bvlshr"} RSHIFT_pa(p1: paddr_t, p2: paddr_t) : paddr_t;
function {:bvbuiltin "bvashr"} ARSHIFT_pa(p1: paddr_t, p2: paddr_t) : paddr_t;
function {:bvbuiltin "bvand"} AND_pa(p1: paddr_t, p2: paddr_t) : paddr_t;
function {:bvbuiltin "bvor"} OR_pa(p1: paddr_t, p2: paddr_t) : paddr_t;
function {:bvbuiltin "bvxor"} XOR_pa(p1: paddr_t, p2: paddr_t) : paddr_t;
function {:bvbuiltin "bvult"} LT_pa(p1: paddr_t, p2: paddr_t) : bool;
function {:bvbuiltin "bvule"} LE_pa(p1: paddr_t, p2: paddr_t) : bool;
function {:bvbuiltin "bvugt"} GT_pa(p1: paddr_t, p2: paddr_t) : bool;
function {:bvbuiltin "bvuge"} GE_pa(p1: paddr_t, p2: paddr_t) : bool;
function {:bvbuiltin "bvslt"} SLT_pa(p1: paddr_t, p2: paddr_t) : bool;
function {:bvbuiltin "bvsle"} SLE_pa(p1: paddr_t, p2: paddr_t) : bool;
function {:bvbuiltin "bvneg"} NEG_pa(p1: paddr_t) : paddr_t;
function {:bvbuiltin "bvnot"} NOT_pa(p1: paddr_t) : paddr_t;

function {:bvbuiltin "bvadd"} PLUS_vpn(p1: vpn_t, p2: vpn_t) : vpn_t;
function {:bvbuiltin "bvsub"} MINUS_vpn(p1: vpn_t, p2: vpn_t) : vpn_t;
function {:bvbuiltin "bvmul"} TIMES_vpn(p1: vpn_t, p2: vpn_t) : vpn_t;
function {:bvbuiltin "bvmod"} MOD_vpn(p1: vpn_t, p2: vpn_t) : vpn_t;
function {:bvbuiltin "bvsmod"} SMOD_vpn(p1: vpn_t, p2: vpn_t) : vpn_t;
function {:bvbuiltin "bvshl"} LSHIFT_vpn(p1: vpn_t, p2: vpn_t) : vpn_t;
function {:bvbuiltin "bvlshr"} RSHIFT_vpn(p1: vpn_t, p2: vpn_t) : vpn_t;
function {:bvbuiltin "bvashr"} ARSHIFT_vpn(p1: vpn_t, p2: vpn_t) : vpn_t;
function {:bvbuiltin "bvand"} AND_vpn(p1: vpn_t, p2: vpn_t) : vpn_t;
function {:bvbuiltin "bvor"} OR_vpn(p1: vpn_t, p2: vpn_t) : vpn_t;
function {:bvbuiltin "bvxor"} XOR_vpn(p1: vpn_t, p2: vpn_t) : vpn_t;
function {:bvbuiltin "bvult"} LT_vpn(p1: vpn_t, p2: vpn_t) : bool;
function {:bvbuiltin "bvule"} LE_vpn(p1: vpn_t, p2: vpn_t) : bool;
function {:bvbuiltin "bvugt"} GT_vpn(p1: vpn_t, p2: vpn_t) : bool;
function {:bvbuiltin "bvuge"} GE_vpn(p1: vpn_t, p2: vpn_t) : bool;
function {:bvbuiltin "bvslt"} SLT_vpn(p1: vpn_t, p2: vpn_t) : bool;
function {:bvbuiltin "bvsle"} SLE_vpn(p1: vpn_t, p2: vpn_t) : bool;
function {:bvbuiltin "bvneg"} NEG_vpn(p1: vpn_t) : vpn_t;
function {:bvbuiltin "bvnot"} NOT_vpn(p1: vpn_t) : vpn_t;

function {:bvbuiltin "bvadd"} PLUS_vpn0(p1: vpn0_t, p2: vpn0_t) : vpn0_t;
function {:bvbuiltin "bvsub"} MINUS_vpn0(p1: vpn0_t, p2: vpn0_t) : vpn0_t;
function {:bvbuiltin "bvmul"} TIMES_vpn0(p1: vpn0_t, p2: vpn0_t) : vpn0_t;
function {:bvbuiltin "bvmod"} MOD_vpn0(p1: vpn0_t, p2: vpn0_t) : vpn0_t;
function {:bvbuiltin "bvsmod"} SMOD_vpn0(p1: vpn0_t, p2: vpn0_t) : vpn0_t;
function {:bvbuiltin "bvshl"} LSHIFT_vpn0(p1: vpn0_t, p2: vpn0_t) : vpn0_t;
function {:bvbuiltin "bvlshr"} RSHIFT_vpn0(p1: vpn0_t, p2: vpn0_t) : vpn0_t;
function {:bvbuiltin "bvashr"} ARSHIFT_vpn0(p1: vpn0_t, p2: vpn0_t) : vpn0_t;
function {:bvbuiltin "bvand"} AND_vpn0(p1: vpn0_t, p2: vpn0_t) : vpn0_t;
function {:bvbuiltin "bvor"} OR_vpn0(p1: vpn0_t, p2: vpn0_t) : vpn0_t;
function {:bvbuiltin "bvxor"} XOR_vpn0(p1: vpn0_t, p2: vpn0_t) : vpn0_t;
function {:bvbuiltin "bvult"} LT_vpn0(p1: vpn0_t, p2: vpn0_t) : bool;
function {:bvbuiltin "bvule"} LE_vpn0(p1: vpn0_t, p2: vpn0_t) : bool;
function {:bvbuiltin "bvugt"} GT_vpn0(p1: vpn0_t, p2: vpn0_t) : bool;
function {:bvbuiltin "bvuge"} GE_vpn0(p1: vpn0_t, p2: vpn0_t) : bool;
function {:bvbuiltin "bvslt"} SLT_vpn0(p1: vpn0_t, p2: vpn0_t) : bool;
function {:bvbuiltin "bvsle"} SLE_vpn0(p1: vpn0_t, p2: vpn0_t) : bool;
function {:bvbuiltin "bvneg"} NEG_vpn0(p1: vpn0_t) : vpn0_t;
function {:bvbuiltin "bvnot"} NOT_vpn0(p1: vpn0_t) : vpn0_t;

function {:bvbuiltin "bvadd"} PLUS_vpn1(p1: vpn1_t, p2: vpn1_t) : vpn1_t;
function {:bvbuiltin "bvsub"} MINUS_vpn1(p1: vpn1_t, p2: vpn1_t) : vpn1_t;
function {:bvbuiltin "bvmul"} TIMES_vpn1(p1: vpn1_t, p2: vpn1_t) : vpn1_t;
function {:bvbuiltin "bvmod"} MOD_vpn1(p1: vpn1_t, p2: vpn1_t) : vpn1_t;
function {:bvbuiltin "bvsmod"} SMOD_vpn1(p1: vpn1_t, p2: vpn1_t) : vpn1_t;
function {:bvbuiltin "bvshl"} LSHIFT_vpn1(p1: vpn1_t, p2: vpn1_t) : vpn1_t;
function {:bvbuiltin "bvlshr"} RSHIFT_vpn1(p1: vpn1_t, p2: vpn1_t) : vpn1_t;
function {:bvbuiltin "bvashr"} ARSHIFT_vpn1(p1: vpn1_t, p2: vpn1_t) : vpn1_t;
function {:bvbuiltin "bvand"} AND_vpn1(p1: vpn1_t, p2: vpn1_t) : vpn1_t;
function {:bvbuiltin "bvor"} OR_vpn1(p1: vpn1_t, p2: vpn1_t) : vpn1_t;
function {:bvbuiltin "bvxor"} XOR_vpn1(p1: vpn1_t, p2: vpn1_t) : vpn1_t;
function {:bvbuiltin "bvult"} LT_vpn1(p1: vpn1_t, p2: vpn1_t) : bool;
function {:bvbuiltin "bvule"} LE_vpn1(p1: vpn1_t, p2: vpn1_t) : bool;
function {:bvbuiltin "bvugt"} GT_vpn1(p1: vpn1_t, p2: vpn1_t) : bool;
function {:bvbuiltin "bvuge"} GE_vpn1(p1: vpn1_t, p2: vpn1_t) : bool;
function {:bvbuiltin "bvslt"} SLT_vpn1(p1: vpn1_t, p2: vpn1_t) : bool;
function {:bvbuiltin "bvsle"} SLE_vpn1(p1: vpn1_t, p2: vpn1_t) : bool;
function {:bvbuiltin "bvneg"} NEG_vpn1(p1: vpn1_t) : vpn1_t;
function {:bvbuiltin "bvnot"} NOT_vpn1(p1: vpn1_t) : vpn1_t;

function {:bvbuiltin "bvadd"} PLUS_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : vpn1ex_t;
function {:bvbuiltin "bvsub"} MINUS_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : vpn1ex_t;
function {:bvbuiltin "bvmul"} TIMES_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : vpn1ex_t;
function {:bvbuiltin "bvmod"} MOD_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : vpn1ex_t;
function {:bvbuiltin "bvsmod"} SMOD_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : vpn1ex_t;
function {:bvbuiltin "bvshl"} LSHIFT_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : vpn1ex_t;
function {:bvbuiltin "bvlshr"} RSHIFT_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : vpn1ex_t;
function {:bvbuiltin "bvashr"} ARSHIFT_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : vpn1ex_t;
function {:bvbuiltin "bvand"} AND_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : vpn1ex_t;
function {:bvbuiltin "bvor"} OR_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : vpn1ex_t;
function {:bvbuiltin "bvxor"} XOR_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : vpn1ex_t;
function {:bvbuiltin "bvult"} LT_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : bool;
function {:bvbuiltin "bvule"} LE_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : bool;
function {:bvbuiltin "bvugt"} GT_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : bool;
function {:bvbuiltin "bvuge"} GE_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : bool;
function {:bvbuiltin "bvslt"} SLT_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : bool;
function {:bvbuiltin "bvsle"} SLE_vpn1ex(p1: vpn1ex_t, p2: vpn1ex_t) : bool;
function {:bvbuiltin "bvneg"} NEG_vpn1ex(p1: vpn1ex_t) : vpn1ex_t;
function {:bvbuiltin "bvnot"} NOT_vpn1ex(p1: vpn1ex_t) : vpn1ex_t;

function {:bvbuiltin "bvadd"} PLUS_ppn(p1: ppn_t, p2: ppn_t) : ppn_t;
function {:bvbuiltin "bvsub"} MINUS_ppn(p1: ppn_t, p2: ppn_t) : ppn_t;
function {:bvbuiltin "bvmul"} TIMES_ppn(p1: ppn_t, p2: ppn_t) : ppn_t;
function {:bvbuiltin "bvmod"} MOD_ppn(p1: ppn_t, p2: ppn_t) : ppn_t;
function {:bvbuiltin "bvsmod"} SMOD_ppn(p1: ppn_t, p2: ppn_t) : ppn_t;
function {:bvbuiltin "bvshl"} LSHIFT_ppn(p1: ppn_t, p2: ppn_t) : ppn_t;
function {:bvbuiltin "bvlshr"} RSHIFT_ppn(p1: ppn_t, p2: ppn_t) : ppn_t;
function {:bvbuiltin "bvashr"} ARSHIFT_ppn(p1: ppn_t, p2: ppn_t) : ppn_t;
function {:bvbuiltin "bvand"} AND_ppn(p1: ppn_t, p2: ppn_t) : ppn_t;
function {:bvbuiltin "bvor"} OR_ppn(p1: ppn_t, p2: ppn_t) : ppn_t;
function {:bvbuiltin "bvxor"} XOR_ppn(p1: ppn_t, p2: ppn_t) : ppn_t;
function {:bvbuiltin "bvult"} LT_ppn(p1: ppn_t, p2: ppn_t) : bool;
function {:bvbuiltin "bvule"} LE_ppn(p1: ppn_t, p2: ppn_t) : bool;
function {:bvbuiltin "bvugt"} GT_ppn(p1: ppn_t, p2: ppn_t) : bool;
function {:bvbuiltin "bvuge"} GE_ppn(p1: ppn_t, p2: ppn_t) : bool;
function {:bvbuiltin "bvslt"} SLT_ppn(p1: ppn_t, p2: ppn_t) : bool;
function {:bvbuiltin "bvsle"} SLE_ppn(p1: ppn_t, p2: ppn_t) : bool;
function {:bvbuiltin "bvneg"} NEG_ppn(p1: ppn_t) : ppn_t;
function {:bvbuiltin "bvnot"} NOT_ppn(p1: ppn_t) : ppn_t;

function {:bvbuiltin "bvule"} LE_r(p1: region_t, p2: region_t) : bool;
function {:bvbuiltin "bvult"} LT_r(p1: region_t, p2: region_t) : bool;
function {:bvbuiltin "bvadd"} PLUS_r(p1: region_t, p2: region_t) : region_t;

function {:bvbuiltin "bvult"} LT_wpo(p1: wpoffset_t, p2: wpoffset_t) : bool;
function {:bvbuiltin "bvadd"} PLUS_wpo(p1: wpoffset_t, p2: wpoffset_t) : wpoffset_t;

function {:bvbuiltin "bvmul"} TIMES_128(p1: bv128, p2: bv128) : bv128;

/* Helpers */
function {:inline} bv2bool(x: bv1): bool { if (x == 0bv1) then false else true }
function {:inline} bool2bv(x: bool): bv1 { if (!x) then 0bv1 else 1bv1 }

function {:inline} ITE_1(b : bool,  x : bv1,   y : bv1) : bv1 { if (b) then x else y }
function {:inline} ITE_8(b : bool,  x : bv8,   y : bv8) : bv8 { if (b) then x else y }
function {:inline} ITE_16(b : bool, x : bv16, y : bv16) : bv16 { if (b) then x else y }
function {:inline} ITE_32(b : bool, x : bv32, y : bv32) : bv32 { if (b) then x else y }
function {:inline} ITE_64(b : bool, x : bv64, y : bv64) : bv64 { if (b) then x else y }
function {:inline} ITE_128(b : bool, x : bv128, y : bv128) : bv128 { if (b) then x else y }
