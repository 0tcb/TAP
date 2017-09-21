/**********************************
 * CPU State                      *
 **********************************/

var rip  : vaddr_t; //program counter
var reg  : bv32; //is RISCV ISA (restricted to 1 register) Turing complete? we can just make this an int.

/**********************************
 * CPU Operations                 *
 **********************************/

function register_update_function(seed: int) : bv32;

/**********************************
 * CPU Operations                 *
 **********************************/

const cpu_mode_const : riscv_mode_t;
const cpu_mode_pum_const : bool;
const cpu_mode_mxr_const : bool;
axiom cpu_mode_mxr_const == false;

procedure {:inline 1} RISCV_ISA_load(vaddr: vaddr_t) returns (data: word_t, exn: bool)
{
  var cpu_mode: riscv_mode_t;
  var cpu_mode_pum: bool;
  var cpu_mode_mxr: bool;
  var valid: bool;
  var paddr: paddr_t;
  var acl: pte_acl_t;

  havoc cpu_mode; assume cpu_mode != RISCV_MODE_M;
  havoc cpu_mode_pum;
  havoc cpu_mode_mxr;

  //TODO: we need to fix these value
  assume cpu_mode == cpu_mode_const;
  assume cpu_mode_pum == cpu_mode_pum_const;
  assume cpu_mode_mxr == cpu_mode_mxr_const;

  call valid, paddr, acl := translate(vaddr, riscv_access_read, cpu_mode, cpu_mode_pum, cpu_mode_mxr);

  if (valid) {
    data := LOAD_LE_32(mem, paddr);
    exn := false;
  } else {
    exn := true;
  }
}

procedure {:inline 1} RISCV_ISA_store(vaddr: vaddr_t, data: word_t) returns (exn: bool)
  modifies mem;
{
  var cpu_mode: riscv_mode_t;
  var cpu_mode_pum: bool;
  var cpu_mode_mxr: bool;
  var valid: bool;
  var paddr: paddr_t;
  var acl: pte_acl_t;

  havoc cpu_mode; assume cpu_mode != RISCV_MODE_M;
  havoc cpu_mode_pum;
  havoc cpu_mode_mxr;

  //TODO: we need to fix these value
  assume cpu_mode == cpu_mode_const;
  assume cpu_mode_pum == cpu_mode_pum_const;
  assume cpu_mode_mxr == cpu_mode_mxr_const;

  call valid, paddr, acl := translate(vaddr, riscv_access_write, cpu_mode, cpu_mode_pum, cpu_mode_mxr);

  if (valid) {
    call mem := STORE_LE_32(mem, paddr, data);
    exn := false;
  } else {
    exn := true;
  }
}

procedure {:inline 1} RISCV_ISA_misc(seed: int)
  modifies reg;
{
  //update reg. deterministic relative to seed
  reg := register_update_function(seed);
}

