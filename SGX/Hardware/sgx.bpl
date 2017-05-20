/******************** Documentation (from PRM) *********************
EPCM Entry:
  VALID: valid entry?
  R: can enclave read this?
  W: can enclave write this?
  X: can enclave execute this?
  PT: page type: PT_SECS, PT_TCS, PT_REG, PT_VA, PT_TRIM
  ENCLAVESECS: SECS id of the enclave to which the page belongs
  ENCLAVEADDRESS: linear enclave address of the page i.e. which virtual address should map to this page?
  BLOCKED: in blocked state?
  PENDING: in pending state?
  MODIFIED: in modified state?

SECS Entry:
  SIZE: size of enclave (in bytes)
  BASEADDR: enclave base linear address
  SSAFRAMESIZE: size of 1 ssa frame
  MRENCLAVE: measurement register
  MRSIGNER: measurement register extended with the public key that verified the enclave
  ISVPRODID: product id
  ISVSVN: security version number
  EID: enclave id
*/

//********************* Types *********************
type sgx_api_result_t = bv1;
type page_table_map_t = [vaddr_t] wap_addr_t;
type page_table_valid_t = [vaddr_t] bool;
//processor id
type lp_id_t = int;
//(cr_enclave_mode: bool, cr_tcs_pa: wap_addr_t, cr_active_secs: wap_addr_t, cr_elrange: lr_register_t, ssa_pa: wap_addr_t)
type lp_state_t;
//registers, but left abstract
type xstate_t;
type lr_register_t;
type page_t = bv2;
type epcm_entry_t;
type key_t = int;
type sgx_measurement_t = int;
type hashtext_t a; //unary type constructor
type ciphertext_t a;
type mactext_t a;
type attributes_t;
type targetinfo_t;
type report_t;
type report_maced_t;
type keyname_t;
type keyrequest_t;
type einittoken_t;
type sigstruct_t;
type sigstruct_signature_t = ciphertext_t (hashtext_t sigstruct_t);
type sigstruct_signed_t;
type secinfo_t;
type pcmd_t;
type pageinfo_t;
type secs_t;
type tcs_t;

//********************* States *********************
var page_table_map : page_table_map_t;
var page_table_valid : page_table_valid_t;
var curr_lp : lp_id_t;
var xstate : [lp_id_t] xstate_t;
var lp_state : [lp_id_t] lp_state_t;
var mem_secs : [wap_addr_t] secs_t;
var mem_tcs : [wap_addr_t] tcs_t;
var mem_reg : [wap_addr_t] word_t;
var epcm : [wap_addr_t] epcm_entry_t;
var arbitrary_write_count: int;

//********************* Constants *********************
const CSR_INTELPUBKEYHASH : hashtext_t key_t; 
const EPC_LOW  : wap_addr_t; axiom EPC_LOW == 4096bv22; //arbitrary value
const EPC_HIGH : wap_addr_t; axiom EPC_HIGH == 45056bv22; //arbitrary value
const PAGE_SIZE: vaddr_t; axiom PAGE_SIZE == 12bv32;

const dummy_signing_key : key_t;
const sgx_api_invalid_value : sgx_api_result_t; axiom sgx_api_invalid_value == 0bv1;
const sgx_api_success : sgx_api_result_t; axiom sgx_api_success == 1bv1;
const abort_page : wap_addr_t; axiom abort_page == 0bv22;
const dummy_lsrr : lr_register_t;
const dummy_xstate : xstate_t; //const unique dummy_xstate : xstate_t;
const pt_secs : page_t; axiom pt_secs == 0bv2;
const pt_tcs : page_t; axiom pt_tcs == 1bv2;
const pt_reg : page_t; axiom pt_reg == 2bv2;

//********************* Functions *********************

function {:inline} pageof_va(va: vaddr_t) : vaddr_t { va[32:12] ++ 0bv12 } 
function {:inline} pageof_pa(pa: wap_addr_t) : wap_addr_t { pa[22:12] ++ 0bv12 } 

//linear range register: (lbase, lsize)
function Lr_register(lbase: vaddr_t, lsize: vaddr_t) : lr_register_t;
function Lr_register_lbase (lr : lr_register_t) : vaddr_t;
function Lr_register_lsize (lr : lr_register_t) : vaddr_t;
axiom (forall lbase: vaddr_t, lsize: vaddr_t :: {Lr_register(lbase,lsize)}
       Lr_register_lbase(Lr_register(lbase, lsize)) == lbase);
axiom (forall lbase: vaddr_t, lsize: vaddr_t :: {Lr_register(lbase,lsize)}
       Lr_register_lsize(Lr_register(lbase, lsize)) == lsize);
axiom (forall lr: lr_register_t :: {Lr_register_lbase(lr)} {Lr_register_lsize(lr)}
       Lr_register(Lr_register_lbase(lr), Lr_register_lsize(lr)) == lr);

function in_register_range (vaddr_t, lr_register_t) : bool;
axiom (forall la : vaddr_t, lr : lr_register_t :: {in_register_range(la,lr)}
       in_register_range(la,lr) <==> 
       (LE_va(Lr_register_lbase(lr), la) && 
        LT_va(la, PLUS_va(Lr_register_lbase(lr), Lr_register_lsize(lr)))));

//function in_ssa_range(vaddr_t, tcs_t, secs_t): bool;
//axiom (forall la: vaddr_t, tcs: tcs_t, secs: secs_t :: {in_ssa_range(la, tcs, secs)}
//       in_ssa_range(la,tcs, secs) <==> (la >= (Secs_baseaddr(secs) + Tcs_ossa(tcs))) && (la < (Secs_baseaddr(secs) + Tcs_ossa(tcs) + Tcs_nssa(tcs))));

//Enclave related memory: all physical memory is partitioned into EPC memory and non-EPC memory
function is_epc_address (wap_addr_t) : bool;
axiom (forall i: wap_addr_t :: {is_epc_address(i)}
      is_epc_address(i) <==> (LE_wapa(EPC_LOW, i) && LT_wapa(i, EPC_HIGH)));

//********************* Processor *********************
//processor state is type-cast to data when storing to memory
function xstate_to_word(xstate_t) : word_t;
function word_to_xstate(word_t) : xstate_t;
axiom (forall w: word_t :: {word_to_xstate(w)}
    xstate_to_word(word_to_xstate(w)) == w); 
axiom (forall x: xstate_t :: {xstate_to_word(x)}
    word_to_xstate(xstate_to_word(x)) == x);

function Lp_state(cr_enclave_mode: bool,
                  cr_tcs_pa: wap_addr_t,
                  cr_active_secs: wap_addr_t,
                  cr_elrange: lr_register_t,
                  ssa_pa: wap_addr_t)
                  : lp_state_t;
function Lp_state_cr_enclave_mode (lps : lp_state_t) : bool;
function Lp_state_cr_tcs_pa (lps : lp_state_t) : wap_addr_t;
function Lp_state_cr_active_secs (lps : lp_state_t) : wap_addr_t;
function Lp_state_cr_elrange (lps : lp_state_t) : lr_register_t;
function Lp_state_ssa_pa (lps : lp_state_t) : wap_addr_t;
axiom (forall cr_enclave_mode: bool,
              cr_tcs_pa: wap_addr_t,
              cr_active_secs: wap_addr_t,
              cr_elrange: lr_register_t,
              ssa_pa: wap_addr_t ::
              {Lp_state(cr_enclave_mode, cr_tcs_pa, cr_active_secs, cr_elrange, ssa_pa)}
       Lp_state_cr_enclave_mode(Lp_state(cr_enclave_mode, cr_tcs_pa, cr_active_secs, cr_elrange, ssa_pa)) == cr_enclave_mode);
axiom (forall cr_enclave_mode: bool,
              cr_tcs_pa: wap_addr_t,
              cr_active_secs: wap_addr_t,
              cr_elrange: lr_register_t,
              ssa_pa: wap_addr_t ::
              {Lp_state(cr_enclave_mode, cr_tcs_pa, cr_active_secs, cr_elrange, ssa_pa)}
       Lp_state_cr_tcs_pa(Lp_state(cr_enclave_mode, cr_tcs_pa, cr_active_secs, cr_elrange, ssa_pa)) == cr_tcs_pa);
axiom (forall cr_enclave_mode: bool,
              cr_tcs_pa: wap_addr_t,
              cr_active_secs: wap_addr_t,
              cr_elrange: lr_register_t,
              ssa_pa: wap_addr_t ::
              {Lp_state(cr_enclave_mode, cr_tcs_pa, cr_active_secs, cr_elrange, ssa_pa)}
       Lp_state_cr_active_secs(Lp_state(cr_enclave_mode, cr_tcs_pa, cr_active_secs, cr_elrange, ssa_pa)) == cr_active_secs);
axiom (forall cr_enclave_mode: bool,
              cr_tcs_pa: wap_addr_t,
              cr_active_secs: wap_addr_t,
              cr_elrange: lr_register_t,
              ssa_pa: wap_addr_t ::
              {Lp_state(cr_enclave_mode, cr_tcs_pa, cr_active_secs, cr_elrange, ssa_pa)}
       Lp_state_cr_elrange(Lp_state(cr_enclave_mode, cr_tcs_pa, cr_active_secs, cr_elrange, ssa_pa)) == cr_elrange);
axiom (forall cr_enclave_mode: bool,
              cr_tcs_pa: wap_addr_t,
              cr_active_secs: wap_addr_t,
              cr_elrange: lr_register_t,
              ssa_pa: wap_addr_t ::
              {Lp_state(cr_enclave_mode, cr_tcs_pa, cr_active_secs, cr_elrange, ssa_pa)}
       Lp_state_ssa_pa(Lp_state(cr_enclave_mode, cr_tcs_pa, cr_active_secs, cr_elrange, ssa_pa)) == ssa_pa);

axiom (forall lps: lp_state_t ::
              {Lp_state_cr_enclave_mode(lps)}
              {Lp_state_cr_tcs_pa(lps)}
              {Lp_state_cr_active_secs(lps)}
              {Lp_state_cr_elrange(lps)}
              {Lp_state_ssa_pa(lps)}
        Lp_state( Lp_state_cr_enclave_mode(lps),
                  Lp_state_cr_tcs_pa(lps),
                  Lp_state_cr_active_secs(lps),
                  Lp_state_cr_elrange(lps),
                  Lp_state_ssa_pa(lps) ) == lps);


//********************* SGX structs *********************

function Attributes(einittokenkey: bool): attributes_t;
function Attributes_einittokenkey(attributes: attributes_t): bool;
axiom (forall einittokenkey: bool :: 
  {Attributes(einittokenkey)}
  Attributes_einittokenkey(Attributes(einittokenkey)) == einittokenkey);
axiom (forall attributes: attributes_t ::
  {Attributes_einittokenkey(attributes)}
  Attributes(Attributes_einittokenkey(attributes)) == attributes);

function Targetinfo(attributes: attributes_t, measurement: sgx_measurement_t): targetinfo_t;
function Targetinfo_attributes(targetinfo: targetinfo_t): attributes_t;
function Targetinfo_measurement(targetinfo: targetinfo_t): sgx_measurement_t;
axiom (forall attributes: attributes_t, measurement: sgx_measurement_t ::
  {Targetinfo(attributes, measurement)}
  Targetinfo_attributes(Targetinfo(attributes, measurement)) == attributes);
axiom (forall attributes: attributes_t, measurement: sgx_measurement_t ::
  {Targetinfo(attributes, measurement)}
  Targetinfo_measurement(Targetinfo(attributes, measurement)) == measurement);
axiom (forall targetinfo: targetinfo_t ::
  {Targetinfo_attributes(targetinfo)}
  {Targetinfo_measurement(targetinfo)}
  Targetinfo(Targetinfo_attributes(targetinfo), Targetinfo_measurement(targetinfo)) == targetinfo);

function Report(isvprodid: int, isvsvn: int, attributes: attributes_t,
                reportdata: word_t, mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t) : report_t;
function Report_isvprodid(report: report_t): int;
function Report_isvsvn(report: report_t): int;
function Report_attributes(report: report_t): attributes_t;
function Report_reportdata(report: report_t): word_t;
function Report_mrenclave(report: report_t): sgx_measurement_t;
function Report_mrsigner(report: report_t): hashtext_t key_t;
axiom (forall isvprodid: int, isvsvn: int, attributes: attributes_t,
              reportdata: word_t, mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t ::
  {Report(isvprodid, isvsvn, attributes, reportdata, mrenclave, mrsigner)}
  Report_isvprodid(Report(isvprodid, isvsvn, attributes, reportdata, mrenclave, mrsigner)) == isvprodid);
axiom (forall isvprodid: int, isvsvn: int, attributes: attributes_t,
              reportdata: word_t, mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t ::
  {Report(isvprodid, isvsvn, attributes, reportdata, mrenclave, mrsigner)}
  Report_isvsvn(Report(isvprodid, isvsvn, attributes, reportdata, mrenclave, mrsigner)) == isvsvn);
axiom (forall isvprodid: int, isvsvn: int, attributes: attributes_t,
              reportdata: word_t, mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t ::
  {Report(isvprodid, isvsvn, attributes, reportdata, mrenclave, mrsigner)}
  Report_attributes(Report(isvprodid, isvsvn, attributes, reportdata, mrenclave, mrsigner)) == attributes);
axiom (forall isvprodid: int, isvsvn: int, attributes: attributes_t,
              reportdata: word_t, mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t ::
  {Report(isvprodid, isvsvn, attributes, reportdata, mrenclave, mrsigner)}
  Report_reportdata(Report(isvprodid, isvsvn, attributes, reportdata, mrenclave, mrsigner)) == reportdata);
axiom (forall isvprodid: int, isvsvn: int, attributes: attributes_t,
              reportdata: word_t, mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t ::
  {Report(isvprodid, isvsvn, attributes, reportdata, mrenclave, mrsigner)}
  Report_mrenclave(Report(isvprodid, isvsvn, attributes, reportdata, mrenclave, mrsigner)) == mrenclave);
axiom (forall isvprodid: int, isvsvn: int, attributes: attributes_t,
              reportdata: word_t, mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t ::
  {Report(isvprodid, isvsvn, attributes, reportdata, mrenclave, mrsigner)}
  Report_mrsigner(Report(isvprodid, isvsvn, attributes, reportdata, mrenclave, mrsigner)) == mrsigner);
axiom (forall report: report_t ::
  {Report_isvprodid(report)}
  {Report_isvsvn(report)}
  {Report_attributes(report)}
  {Report_reportdata(report)}
  {Report_mrenclave(report)}
  {Report_mrsigner(report)}
  Report(Report_isvprodid(report),
         Report_isvsvn(report),
         Report_attributes(report),
         Report_reportdata(report),
         Report_mrenclave(report),
         Report_mrsigner(report)) == report);


function Report_maced(report: report_t, mac: mactext_t report_t): report_maced_t;
function Report_maced_report(report_maced: report_maced_t): report_t;
function Report_maced_mac(report_maced: report_maced_t): mactext_t report_t;
axiom (forall report: report_t, mac: mactext_t report_t ::
  {Report_maced(report, mac)}
  Report_maced_report(Report_maced(report, mac)) == report);
axiom (forall report: report_t, mac: mactext_t report_t ::
  {Report_maced(report, mac)}
  Report_maced_mac(Report_maced(report, mac)) == mac);
axiom (forall report_maced: report_maced_t ::
  {Report_maced_report(report_maced)}
  {Report_maced_mac(report_maced)}
  Report_maced(Report_maced_report(report_maced), 
               Report_maced_mac(report_maced)) == report_maced);

const unique launch_key : keyname_t;
const unique provision_key : keyname_t;
const unique provision_seal_key : keyname_t;
const unique report_key : keyname_t;
const unique seal_key : keyname_t;

function Keyrequest(keyname: keyname_t, isvsvn: int, 
                    keypolicy_mrenclave: bool, keypolicy_mrsigner: bool): keyrequest_t; 
function Keyrequest_keyname(keyrequest: keyrequest_t) : keyname_t;
function Keyrequest_isvsvn(keyrequest: keyrequest_t) : int;
function Keyrequest_keypolicy_mrenclave(keyrequest: keyrequest_t) : bool;
function Keyrequest_keypolicy_mrsigner(keyrequest: keyrequest_t) : bool;
axiom (forall keyname: keyname_t, isvsvn: int, 
              keypolicy_mrenclave: bool, keypolicy_mrsigner: bool :: 
  {Keyrequest(keyname, isvsvn, keypolicy_mrenclave, keypolicy_mrsigner)}
  Keyrequest_keyname(Keyrequest(keyname, isvsvn, keypolicy_mrenclave, keypolicy_mrsigner)) == keyname);
axiom (forall keyname: keyname_t, isvsvn: int, 
              keypolicy_mrenclave: bool, keypolicy_mrsigner: bool :: 
  {Keyrequest(keyname, isvsvn, keypolicy_mrenclave, keypolicy_mrsigner)}
  Keyrequest_isvsvn(Keyrequest(keyname, isvsvn, keypolicy_mrenclave, keypolicy_mrsigner)) == isvsvn);
axiom (forall keyname: keyname_t, isvsvn: int, 
              keypolicy_mrenclave: bool, keypolicy_mrsigner: bool :: 
  {Keyrequest(keyname, isvsvn, keypolicy_mrenclave, keypolicy_mrsigner)}
  Keyrequest_keypolicy_mrenclave(Keyrequest(keyname, isvsvn, keypolicy_mrenclave, keypolicy_mrsigner)) == keypolicy_mrenclave);
axiom (forall keyname: keyname_t, isvsvn: int, 
              keypolicy_mrenclave: bool, keypolicy_mrsigner: bool :: 
  {Keyrequest(keyname, isvsvn, keypolicy_mrenclave, keypolicy_mrsigner)}
  Keyrequest_keypolicy_mrsigner(Keyrequest(keyname, isvsvn, keypolicy_mrenclave, keypolicy_mrsigner)) == keypolicy_mrsigner);
axiom (forall keyrequest: keyrequest_t ::
  {Keyrequest_keyname(keyrequest)}
  {Keyrequest_isvsvn(keyrequest)}
  {Keyrequest_keypolicy_mrenclave(keyrequest)}
  {Keyrequest_keypolicy_mrsigner(keyrequest)}
  Keyrequest(Keyrequest_keyname(keyrequest),
             Keyrequest_isvsvn(keyrequest),
             Keyrequest_keypolicy_mrenclave(keyrequest),
             Keyrequest_keypolicy_mrsigner(keyrequest)) == keyrequest);

function Einittoken(valid: bool, attributes: attributes_t, 
                    mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t) : einittoken_t;
function Einittoken_valid(einittoken: einittoken_t): bool;
function Einittoken_attributes(einittoken: einittoken_t): attributes_t;
function Einittoken_mrenclave(einittoken: einittoken_t): sgx_measurement_t;
function Einittoken_mrsigner(einittoken: einittoken_t): hashtext_t key_t;
axiom (forall valid: bool, attributes: attributes_t, mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t ::
  {Einittoken(valid, attributes, mrenclave, mrsigner)}
  Einittoken_valid(Einittoken(valid, attributes, mrenclave, mrsigner)) == valid);
axiom (forall valid: bool, attributes: attributes_t, mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t ::
  {Einittoken(valid, attributes, mrenclave, mrsigner)}
  Einittoken_attributes(Einittoken(valid, attributes, mrenclave, mrsigner)) == attributes);
axiom (forall valid: bool, attributes: attributes_t, mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t ::
  {Einittoken(valid, attributes, mrenclave, mrsigner)}
  Einittoken_mrenclave(Einittoken(valid, attributes, mrenclave, mrsigner)) == mrenclave);
axiom (forall valid: bool, attributes: attributes_t, mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t ::
  {Einittoken(valid, attributes, mrenclave, mrsigner)}
  Einittoken_mrsigner(Einittoken(valid, attributes, mrenclave, mrsigner)) == mrsigner);
axiom (forall einittoken: einittoken_t ::
  {Einittoken_valid(einittoken)}
  {Einittoken_attributes(einittoken)}
  {Einittoken_mrenclave(einittoken)}
  {Einittoken_mrsigner(einittoken)}
  Einittoken(Einittoken_valid(einittoken),
             Einittoken_attributes(einittoken),
             Einittoken_mrenclave(einittoken),
             Einittoken_mrsigner(einittoken)) == einittoken);

function Sigstruct(modulus: key_t, enclavehash: sgx_measurement_t,
                   attributes: attributes_t, isvprodid: int, isvsvn: int) : sigstruct_t; 
function Sigstruct_modulus(sigstruct_t) : key_t;
function Sigstruct_enclavehash(sigstruct_t): sgx_measurement_t;
function Sigstruct_attributes(sigstruct_t): attributes_t;
function Sigstruct_isvprodid(sigstruct_t): int;
function Sigstruct_isvsvn(sigstruct_t): int;
axiom (forall modulus: key_t, enclavehash: sgx_measurement_t,
              attributes: attributes_t, isvprodid: int, isvsvn: int ::
  {Sigstruct(modulus, enclavehash, attributes, isvprodid, isvsvn)}
  Sigstruct_modulus(Sigstruct(modulus, enclavehash, attributes, isvprodid, isvsvn)) == modulus);
axiom (forall modulus: key_t, enclavehash: sgx_measurement_t,
              attributes: attributes_t, isvprodid: int, isvsvn: int ::
  {Sigstruct(modulus, enclavehash, attributes, isvprodid, isvsvn)}
  Sigstruct_enclavehash(Sigstruct(modulus, enclavehash, attributes, isvprodid, isvsvn)) == enclavehash);
axiom (forall modulus: key_t, enclavehash: sgx_measurement_t,
              attributes: attributes_t, isvprodid: int, isvsvn: int ::
  {Sigstruct(modulus, enclavehash, attributes, isvprodid, isvsvn)}
  Sigstruct_attributes(Sigstruct(modulus, enclavehash, attributes, isvprodid, isvsvn)) == attributes);
axiom (forall modulus: key_t, enclavehash: sgx_measurement_t,
              attributes: attributes_t, isvprodid: int, isvsvn: int ::
  {Sigstruct(modulus, enclavehash, attributes, isvprodid, isvsvn)}
  Sigstruct_isvprodid(Sigstruct(modulus, enclavehash, attributes, isvprodid, isvsvn)) == isvprodid);
axiom (forall modulus: key_t, enclavehash: sgx_measurement_t,
              attributes: attributes_t, isvprodid: int, isvsvn: int ::
  {Sigstruct(modulus, enclavehash, attributes, isvprodid, isvsvn)}
  Sigstruct_isvsvn(Sigstruct(modulus, enclavehash, attributes, isvprodid, isvsvn)) == isvsvn);
axiom (forall sigstruct: sigstruct_t ::
  {Sigstruct_modulus(sigstruct)}
  {Sigstruct_enclavehash(sigstruct)}
  {Sigstruct_attributes(sigstruct)}
  {Sigstruct_isvprodid(sigstruct)}
  {Sigstruct_isvsvn(sigstruct)}
  Sigstruct(Sigstruct_modulus(sigstruct),
            Sigstruct_enclavehash(sigstruct),
            Sigstruct_attributes(sigstruct),
            Sigstruct_isvprodid(sigstruct),
            Sigstruct_isvsvn(sigstruct)) == sigstruct);

function Sigstruct_signed(signature: sigstruct_signature_t, sigstruct: sigstruct_t) : sigstruct_signed_t;
function Sigstruct_signed_signature(sigstruct_signed_t): sigstruct_signature_t;
function Sigstruct_signed_sigstruct(sigstruct_signed_t): sigstruct_t;
axiom (forall signature: sigstruct_signature_t, sigstruct: sigstruct_t ::
  {Sigstruct_signed(signature, sigstruct)}
  Sigstruct_signed_signature(Sigstruct_signed(signature, sigstruct)) == signature);
axiom (forall signature: sigstruct_signature_t, sigstruct: sigstruct_t ::
  {Sigstruct_signed(signature, sigstruct)}
  Sigstruct_signed_sigstruct(Sigstruct_signed(signature, sigstruct)) == sigstruct);
axiom (forall sigstruct_signed: sigstruct_signed_t ::
  {Sigstruct_signed_signature(sigstruct_signed)}
  {Sigstruct_signed_sigstruct(sigstruct_signed)}
  Sigstruct_signed(Sigstruct_signed_signature(sigstruct_signed),
                   Sigstruct_signed_sigstruct(sigstruct_signed)) == sigstruct_signed);

function Secinfo(flags_r: bool, flags_w: bool, flags_x: bool, flags_pt: page_t): secinfo_t;
function Secinfo_flags_r(secinfo: secinfo_t): bool;
function Secinfo_flags_w(secinfo: secinfo_t): bool;
function Secinfo_flags_x(secinfo: secinfo_t): bool;
function Secinfo_flags_pt(secinfo: secinfo_t) : page_t;
axiom (forall flags_r: bool, flags_w: bool, flags_x: bool, flags_pt: page_t ::
      {Secinfo(flags_r, flags_w, flags_x, flags_pt)}
      Secinfo_flags_r(Secinfo(flags_r, flags_w, flags_x, flags_pt)) == flags_r);
axiom (forall flags_r: bool, flags_w: bool, flags_x: bool, flags_pt: page_t ::
      {Secinfo(flags_r, flags_w, flags_x, flags_pt)}
      Secinfo_flags_w(Secinfo(flags_r, flags_w, flags_x, flags_pt)) == flags_w);
axiom (forall flags_r: bool, flags_w: bool, flags_x: bool, flags_pt: page_t ::
      {Secinfo(flags_r, flags_w, flags_x, flags_pt)}
      Secinfo_flags_x(Secinfo(flags_r, flags_w, flags_x, flags_pt)) == flags_x);
axiom (forall flags_r: bool, flags_w: bool, flags_x: bool, flags_pt: page_t ::
      {Secinfo(flags_r, flags_w, flags_x, flags_pt)}
      Secinfo_flags_pt(Secinfo(flags_r, flags_w, flags_x, flags_pt)) == flags_pt);
axiom (forall secinfo: secinfo_t ::
       {Secinfo_flags_r(secinfo)}
       {Secinfo_flags_w(secinfo)}
       {Secinfo_flags_x(secinfo)}
       {Secinfo_flags_pt(secinfo)}
       Secinfo(Secinfo_flags_r(secinfo),
               Secinfo_flags_w(secinfo),
               Secinfo_flags_x(secinfo),
               Secinfo_flags_pt(secinfo)) == secinfo);

function Pageinfo(linaddr: vaddr_t, srcpge: vaddr_t, 
                  secinfo: secinfo_t, pcmd: pcmd_t, secs: wap_addr_t): pageinfo_t;
function Pageinfo_linaddr(pageinfo: pageinfo_t) : vaddr_t;
function Pageinfo_srcpge(pageinfo: pageinfo_t) : vaddr_t;
function Pageinfo_secinfo(pageinfo: pageinfo_t) : secinfo_t;
function Pageinfo_pcmd(pageinfo: pageinfo_t) : pcmd_t;
function Pageinfo_secs(pageinfo: pageinfo_t) : wap_addr_t;
axiom (forall linaddr: vaddr_t, srcpge: vaddr_t, 
              secinfo: secinfo_t, pcmd: pcmd_t, secs: wap_addr_t ::
       {Pageinfo(linaddr, srcpge, secinfo, pcmd, secs)}
       Pageinfo_linaddr(Pageinfo(linaddr, srcpge, secinfo, pcmd, secs)) == linaddr);
axiom (forall linaddr: vaddr_t, srcpge: vaddr_t, 
              secinfo: secinfo_t, pcmd: pcmd_t, secs: wap_addr_t ::
       {Pageinfo(linaddr, srcpge, secinfo, pcmd, secs)}
       Pageinfo_srcpge(Pageinfo(linaddr, srcpge, secinfo, pcmd, secs)) == srcpge);
axiom (forall linaddr: vaddr_t, srcpge: vaddr_t, 
              secinfo: secinfo_t, pcmd: pcmd_t, secs: wap_addr_t ::
       {Pageinfo(linaddr, srcpge, secinfo, pcmd, secs)}
       Pageinfo_secinfo(Pageinfo(linaddr, srcpge, secinfo, pcmd, secs)) == secinfo);
axiom (forall linaddr: vaddr_t, srcpge: vaddr_t, 
              secinfo: secinfo_t, pcmd: pcmd_t, secs: wap_addr_t ::
       {Pageinfo(linaddr, srcpge, secinfo, pcmd, secs)}
       Pageinfo_pcmd(Pageinfo(linaddr, srcpge, secinfo, pcmd, secs)) == pcmd);
axiom (forall linaddr: vaddr_t, srcpge: vaddr_t, 
              secinfo: secinfo_t, pcmd: pcmd_t, secs: wap_addr_t ::
       {Pageinfo(linaddr, srcpge, secinfo, pcmd, secs)}
       Pageinfo_secs(Pageinfo(linaddr, srcpge, secinfo, pcmd, secs)) == secs);
axiom (forall pageinfo: pageinfo_t ::
       {Pageinfo_linaddr(pageinfo)}
       {Pageinfo_srcpge(pageinfo)}
       {Pageinfo_secinfo(pageinfo)}
       {Pageinfo_pcmd(pageinfo)}
       {Pageinfo_secs(pageinfo)}
       Pageinfo(Pageinfo_linaddr(pageinfo),
                Pageinfo_srcpge(pageinfo),
                Pageinfo_secinfo(pageinfo),
                Pageinfo_pcmd(pageinfo),
                Pageinfo_secs(pageinfo)) == pageinfo);

function Secs(baseaddr: vaddr_t, size: vaddr_t, initialized: bool, 
              mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t, 
              isvprodid: int, isvsvn: int,
              attributes: attributes_t) : secs_t;
function Secs_baseaddr (secs : secs_t) : vaddr_t;
function Secs_size (secs: secs_t) : vaddr_t;
function Secs_initialized (secs: secs_t) : bool;
function Secs_mrenclave (secs: secs_t) : sgx_measurement_t;
function Secs_mrsigner (secs: secs_t) : hashtext_t key_t;
function Secs_isvprodid (secs: secs_t) : int;
function Secs_isvsvn (secs: secs_t) : int;
function Secs_attributes (secs: secs_t) : attributes_t;
axiom (forall baseaddr: vaddr_t, size: vaddr_t, initialized: bool, 
              mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t, 
              isvprodid: int, isvsvn: int, attributes: attributes_t ::
       {Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)}
       Secs_baseaddr(Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)) == baseaddr);
axiom (forall baseaddr: vaddr_t, size: vaddr_t, initialized: bool, 
              mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t, 
              isvprodid: int, isvsvn: int, attributes: attributes_t ::
       {Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)}
       Secs_size(Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)) == size);
axiom (forall baseaddr: vaddr_t, size: vaddr_t, initialized: bool, 
              mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t, 
              isvprodid: int, isvsvn: int, attributes: attributes_t ::
       {Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)}
       Secs_initialized(Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)) == initialized);
axiom (forall baseaddr: vaddr_t, size: vaddr_t, initialized: bool, 
              mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t, 
              isvprodid: int, isvsvn: int, attributes: attributes_t ::
       {Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)}
       Secs_mrenclave(Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)) == mrenclave);
axiom (forall baseaddr: vaddr_t, size: vaddr_t, initialized: bool, 
              mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t, 
              isvprodid: int, isvsvn: int, attributes: attributes_t ::
       {Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)}
       Secs_mrsigner(Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)) == mrsigner);
axiom (forall baseaddr: vaddr_t, size: vaddr_t, initialized: bool, 
              mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t, 
              isvprodid: int, isvsvn: int, attributes: attributes_t ::
       {Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)}
       Secs_isvprodid(Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)) == isvprodid);
axiom (forall baseaddr: vaddr_t, size: vaddr_t, initialized: bool, 
              mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t, 
              isvprodid: int, isvsvn: int, attributes: attributes_t ::
       {Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)}
       Secs_isvsvn(Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)) == isvsvn);
axiom (forall baseaddr: vaddr_t, size: vaddr_t, initialized: bool, 
              mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t, 
              isvprodid: int, isvsvn: int, attributes: attributes_t ::
       {Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)}
       Secs_attributes(Secs(baseaddr, size, initialized, mrenclave, mrsigner, isvprodid, isvsvn, attributes)) == attributes);
axiom (forall secs: secs_t ::
       {Secs_baseaddr(secs)}
       {Secs_size(secs)}
       {Secs_initialized(secs)}
       {Secs_mrenclave(secs)}
       {Secs_mrsigner(secs)}
       {Secs_isvprodid(secs)}
       {Secs_isvsvn(secs)}
       {Secs_attributes(secs)}
       Secs(Secs_baseaddr(secs), Secs_size(secs), Secs_initialized(secs), 
            Secs_mrenclave(secs), Secs_mrsigner(secs), 
            Secs_isvprodid(secs), Secs_isvsvn(secs), Secs_attributes(secs)) == secs);

function Tcs(active: bool, interrupted: bool, ossa: vaddr_t, nssa: vaddr_t, cssa: vaddr_t) : tcs_t;
function Tcs_active (tcs : tcs_t) : bool;
function Tcs_interrupted (tcs : tcs_t) : bool;
function Tcs_ossa (tcs : tcs_t) : vaddr_t;
function Tcs_nssa (tcs : tcs_t) : vaddr_t;
function Tcs_cssa (tcs : tcs_t) : vaddr_t;
axiom (forall active: bool, interrupted: bool, ossa: vaddr_t, nssa: vaddr_t, cssa: vaddr_t ::
       {Tcs(active, interrupted, ossa, nssa, cssa)}
       Tcs_active(Tcs(active, interrupted, ossa, nssa, cssa)) == active);
axiom (forall active: bool, interrupted: bool, ossa: vaddr_t, nssa: vaddr_t, cssa: vaddr_t ::
       {Tcs(active, interrupted, ossa, nssa, cssa)}
       Tcs_interrupted(Tcs(active, interrupted, ossa, nssa, cssa)) == interrupted);
axiom (forall active: bool, interrupted: bool, ossa: vaddr_t, nssa: vaddr_t, cssa: vaddr_t ::
       {Tcs(active, interrupted, ossa, nssa, cssa)}
       Tcs_ossa(Tcs(active, interrupted, ossa, nssa, cssa)) == ossa);
axiom (forall active: bool, interrupted: bool, ossa: vaddr_t, nssa: vaddr_t, cssa: vaddr_t ::
       {Tcs(active, interrupted, ossa, nssa, cssa)}
       Tcs_nssa(Tcs(active, interrupted, ossa, nssa, cssa)) == nssa);
axiom (forall active: bool, interrupted: bool, ossa: vaddr_t, nssa: vaddr_t, cssa: vaddr_t ::
       {Tcs(active, interrupted, ossa, nssa, cssa)}
       Tcs_cssa(Tcs(active, interrupted, ossa, nssa, cssa)) == cssa);
axiom (forall tcs: tcs_t ::
       {Tcs_active(tcs)}
       {Tcs_interrupted(tcs)}
       {Tcs_ossa(tcs)}
       {Tcs_nssa(tcs)}
       {Tcs_cssa(tcs)}
       Tcs(Tcs_active(tcs), Tcs_interrupted(tcs), Tcs_ossa(tcs), Tcs_nssa(tcs), Tcs_cssa(tcs)) == tcs);

//this is meant to be used for writes made by hardware within an SGX instruction. They don't need access permission checks.
function arbitrary_secs_val(int): secs_t;
function arbitrary_tcs_val(int): tcs_t;
function arbitrary_reg_val(int): word_t;

procedure {:inline 1} unchecked_write_secs(pa: wap_addr_t, val: secs_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs; 
{
  mem_secs[pa] := val;
  mem_reg[pa]  := arbitrary_reg_val(arbitrary_write_count);
  mem_tcs[pa]  := arbitrary_tcs_val(arbitrary_write_count);
  arbitrary_write_count := arbitrary_write_count + 1;
}

procedure {:inline 1} unchecked_write_tcs(pa: wap_addr_t, val: tcs_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs; 
{
  mem_tcs[pa] := val;
  mem_reg[pa]  := arbitrary_reg_val(arbitrary_write_count);
  mem_secs[pa]  := arbitrary_secs_val(arbitrary_write_count);
  arbitrary_write_count := arbitrary_write_count + 1;
}

procedure {:inline 1} unchecked_write_reg(pa: wap_addr_t, val: word_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs; 
{
  mem_reg[pa] := val;
  mem_secs[pa]  := arbitrary_secs_val(arbitrary_write_count);
  mem_tcs[pa]  := arbitrary_tcs_val(arbitrary_write_count);
  arbitrary_write_count := arbitrary_write_count + 1;
}

function Epcm(valid: bool, r: bool, w: bool, x: bool, pt: page_t, enclavesecs: wap_addr_t, enclaveaddress: vaddr_t) : epcm_entry_t;
function Epcm_valid(epcm_entry : epcm_entry_t) : bool;
function Epcm_R(epcm_entry : epcm_entry_t): bool;
function Epcm_W(epcm_entry : epcm_entry_t): bool;
function Epcm_X(epcm_entry : epcm_entry_t): bool;
function Epcm_pt (epcm_entry : epcm_entry_t) : page_t;
function Epcm_enclavesecs (epcm_entry : epcm_entry_t) : wap_addr_t;
function Epcm_enclaveaddress (epcm_entry : epcm_entry_t) : vaddr_t;
axiom (forall valid: bool, r: bool, w: bool, x: bool, pt: page_t, enclavesecs: wap_addr_t, enclaveaddress: vaddr_t ::
       {Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)}
       Epcm_valid(Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)) == valid);
axiom (forall valid: bool, r: bool, w: bool, x: bool, pt: page_t, enclavesecs: wap_addr_t, enclaveaddress: vaddr_t ::
       {Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)}
       Epcm_R(Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)) == r);
axiom (forall valid: bool, r: bool, w: bool, x: bool, pt: page_t, enclavesecs: wap_addr_t, enclaveaddress: vaddr_t ::
       {Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)}
       Epcm_W(Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)) == w);
axiom (forall valid: bool, r: bool, w: bool, x: bool, pt: page_t, enclavesecs: wap_addr_t, enclaveaddress: vaddr_t ::
       {Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)}
       Epcm_X(Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)) == x);
axiom (forall valid: bool, r: bool, w: bool, x: bool, pt: page_t, enclavesecs: wap_addr_t, enclaveaddress: vaddr_t ::
       {Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)}
       Epcm_pt(Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)) == pt);
axiom (forall valid: bool, r: bool, w: bool, x: bool, pt: page_t, enclavesecs: wap_addr_t, enclaveaddress: vaddr_t ::
       {Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)}
       Epcm_enclavesecs(Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)) == enclavesecs);
axiom (forall valid: bool, r: bool, w: bool, x: bool, pt: page_t, enclavesecs: wap_addr_t, enclaveaddress: vaddr_t ::
       {Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)}
       Epcm_enclaveaddress(Epcm(valid, r, w, x, pt, enclavesecs, enclaveaddress)) == enclaveaddress);
axiom (forall epcm_entry: epcm_entry_t ::
       {Epcm_valid(epcm_entry)}
       {Epcm_R(epcm_entry)}
       {Epcm_W(epcm_entry)}
       {Epcm_X(epcm_entry)}
       {Epcm_pt(epcm_entry)}
       {Epcm_enclavesecs(epcm_entry)}
       {Epcm_enclaveaddress(epcm_entry)}
       Epcm(Epcm_valid(epcm_entry),
            Epcm_R(epcm_entry),
            Epcm_W(epcm_entry),
            Epcm_X(epcm_entry),
            Epcm_pt(epcm_entry),
            Epcm_enclavesecs(epcm_entry),
            Epcm_enclaveaddress(epcm_entry)) == 
       epcm_entry);

const dummy_epcm : epcm_entry_t;
axiom dummy_epcm == Epcm(false, false, false, false, pt_reg, abort_page, 0bv32);


/* FIXME: access control requirements from the PRM
   - All memory accesses must obey the segmentation and paging policies set by the OS / VMM
   - Code fetches from inside and enclave to linear address outside that enclave results in #GP(0)
   - Non-enclave accesses to EPC memory results in abort page semantics
   - Direct access to EPC page must conform to the security attributes which were established when those pages were added to EPC
     - Target must belong to the same enclave
     - RWX of the requested access conforms with the RWX of target page
     - Target page must not have restricted page type pt_secs, pt_tcs, pt_va
     - Target EPC page must not be blocked
*/
procedure {:inline 1} is_accessible(lp: lp_id_t, la: vaddr_t) returns (result: bool)
{
  var pa : wap_addr_t; //pagetable[la]
  var ea : bool; //is this access to enclave memory?
  var mapped_la : bool; //does pagetable map this to an address != abort_page 

  ea := Lp_state_cr_enclave_mode(lp_state[lp]) && 
        in_register_range(la, Lp_state_cr_elrange(lp_state[lp]));
  pa := page_table_map[la];
  mapped_la := page_table_valid[la];
  result := mapped_la && 
            (ea ==> ((Epcm_valid(epcm[pageof_pa(pa)]) && is_epc_address(pa)) &&
                      Epcm_pt(epcm[pageof_pa(pa)]) == pt_reg &&
                      Epcm_enclavesecs(epcm[pageof_pa(pa)]) == Lp_state_cr_active_secs(lp_state[lp]) &&
                      Epcm_enclaveaddress(epcm[pageof_pa(pa)]) == pageof_va(la)));
}

procedure {:inline 1} translate(la: vaddr_t) returns (result: wap_addr_t)
{
  var ea : bool;
  var pa : wap_addr_t;
  var accessible : bool;

  call accessible := is_accessible(curr_lp, la);

  ea := Lp_state_cr_enclave_mode(lp_state[curr_lp]) && 
        in_register_range(la, Lp_state_cr_elrange(lp_state[curr_lp]));

  pa := page_table_map[la];

  if (!page_table_valid[la] || !accessible || (!ea && is_epc_address(pa))) {
    result := abort_page;
  } else { 
    result := pa;
  }
}

//********************* Helper predicates *********************
//Is cpu represented by lps running an enclave thread whose secs is pa?
function thread_in_enclave(lp_state_t, wap_addr_t) : bool;
axiom (forall lps: lp_state_t, pa: wap_addr_t ::
  {thread_in_enclave(lps, pa)}
  thread_in_enclave(lps,pa) <==> 
  (Lp_state_cr_enclave_mode(lps) && (Lp_state_cr_active_secs(lps) == pa)));

function no_threads_in_enclave([lp_id_t] lp_state_t, wap_addr_t) : bool;
axiom (forall lp_state : [lp_id_t] lp_state_t, pa: wap_addr_t ::
  {no_threads_in_enclave(lp_state, pa)}
  no_threads_in_enclave(lp_state, pa) <==>
  (forall lp: lp_id_t :: !thread_in_enclave(lp_state[lp], pa))); 

function page_in_enclave(epcm_entry_t, wap_addr_t, wap_addr_t) : bool;
axiom (forall epcm_entry : epcm_entry_t, pa: wap_addr_t, ps: wap_addr_t ::
  {page_in_enclave(epcm_entry, pa, ps)}
  page_in_enclave(epcm_entry, pa, ps) <==> 
  (is_epc_address(pa) && 
   Epcm_valid(epcm_entry) && 
   Epcm_enclavesecs(epcm_entry) == ps && 
   pa != ps));

function no_pages_in_enclave([wap_addr_t] epcm_entry_t, wap_addr_t) : bool;
axiom (forall epcm: [wap_addr_t] epcm_entry_t, ps: wap_addr_t ::
  {no_pages_in_enclave(epcm, ps)}
  no_pages_in_enclave(epcm, ps) <==>
  (forall pa: wap_addr_t :: !page_in_enclave(epcm[pageof_pa(pa)], pa, ps)));

function cssa_addr(secs_t, tcs_t) : vaddr_t;
axiom (forall secs: secs_t, tcs: tcs_t ::
  {cssa_addr(secs,tcs)}
  cssa_addr(secs,tcs) ==
  PLUS_va(Secs_baseaddr(secs),
    PLUS_va(LSHIFT_va(Tcs_ossa(tcs), PAGE_SIZE),
            LSHIFT_va(Tcs_cssa(tcs), PAGE_SIZE))));

function pssa_addr(secs_t, tcs_t) : vaddr_t;
axiom (forall secs: secs_t, tcs: tcs_t ::
  {pssa_addr(secs,tcs)}
  pssa_addr(secs,tcs) ==
  MINUS_va(cssa_addr(secs,tcs), LSHIFT_va(k1_vaddr_t, PAGE_SIZE))); 

//axiom constraining sha256 to be injective
function sha256(val: int) : sgx_measurement_t;
axiom (forall val1: int, val2: int ::
  {sha256(val1), sha256(val2)}
  (val1 != val2 ==> sha256(val1) != sha256(val2)));

function cmac<a>(k: key_t, x: a) : mactext_t a;
axiom (forall <a> k: key_t, x1: a, x2: a :: 
  {cmac(k,x1), cmac(k,x2)}
  (x1 != x2 ==> cmac(k,x1) != cmac(k,x2)));

axiom (forall val1: int, val2: int ::
  {sha256(val1), sha256(val2)}
  (val1 != val2 ==> sha256(val1) != sha256(val2)));

//axiom constraining chained sha256 to be injective
function sha256update(prev: sgx_measurement_t, update: int) : sgx_measurement_t;
axiom (forall prev1: sgx_measurement_t, update1: int, prev2: sgx_measurement_t, update2: int ::
  {sha256update(prev1,update1), sha256update(prev2,update2)}
  (prev1 != prev2 || update1 != update2) ==>
  (sha256update(prev1,update1) != sha256update(prev2,update2)));

//injective axiom for hash (we use hash only when its unclear which hash algorithm Intel is using)
function hash<a>(x: a) : hashtext_t a;
axiom (forall <a> x1: a, x2: a :: {hash(x1), hash(x2)}
       (x1 != x2 ==> hash(x1) != hash(x2)));

function derive_key_ereport(attributes: attributes_t, measurement: sgx_measurement_t): key_t;
function derive_key_egetkey(keyname: keyname_t, 
                            isvprodid: int, isvsvn: int, attributes: attributes_t, 
                            mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t): key_t;
axiom (forall attr1: attributes_t, meas1: sgx_measurement_t,
              keyname: keyname_t, isvprodid: int, isvsvn: int,
              attr2: attributes_t, mrenclave: sgx_measurement_t, mrsigner: hashtext_t key_t ::
              {derive_key_ereport(attr1, meas1), derive_key_egetkey(keyname, isvprodid, isvsvn, attr2, mrenclave, mrsigner)}
              (attr1 == attr2 && meas1 == mrenclave && keyname == report_key) ==>
              (derive_key_ereport(attr1, meas1) == derive_key_egetkey(keyname, isvprodid, isvsvn, attr2, mrenclave, mrsigner)));


function decrypt<a>(key: key_t, ciphertext: ciphertext_t a): a;
function encrypt<a>(key: key_t, p: a): ciphertext_t a;
axiom (forall <a> k: key_t, c: ciphertext_t a :: {decrypt(k, c)} encrypt(k, decrypt(k, c)) == c);
axiom (forall <a> k: key_t, p: a :: {encrypt(k,p)} decrypt(k, encrypt(k, p)) == p);

//concatenation must be injective
function concat_two_int_to_one(fst: int, snd: int) : int;
axiom (forall fst1: int, fst2: int, snd1: int, snd2: int ::
  {concat_two_int_to_one(fst1, snd1), concat_two_int_to_one(fst2, snd2)}
  (fst1 != fst2 || snd1 != snd2) ==> (concat_two_int_to_one(fst1,snd1) != concat_two_int_to_one(fst2,snd2)));

function vaddr_to_int(v: vaddr_t) : int;

//cast a regular page to an int
function reg_to_int(val: word_t) : int;
//would like the cast to be one-to-one
axiom (forall val1: word_t, val2: word_t ::
  {reg_to_int(val1), reg_to_int(val2)}
  (val1 != val2 ==> reg_to_int(val1) != reg_to_int(val2)));

//cast a regular page to an int
function tcs_to_int(val: tcs_t) : int;
//would like the cast to be one-to-one
axiom (forall val1: tcs_t, val2: tcs_t ::
  {tcs_to_int(val1), tcs_to_int(val2)}
  (val1 != val2 ==> tcs_to_int(val1) != tcs_to_int(val2)));


//********************* SGX Instructions *********************

procedure {:inline 1} ecreate_unchecked(la: vaddr_t, secs: secs_t) 
modifies epcm, mem_secs, mem_reg, mem_tcs, arbitrary_write_count;
{
  var pa: wap_addr_t;
  var measurement : sgx_measurement_t; //computing value for mrenclave
  var ssaframesize : int;

  pa := page_table_map[la];

  ssaframesize := 1; //FIXME: This is a field within SECS, and not a constant
  //measurement := Secs_mrenclave(secs);
  //measurement := sha256update(measurement, concat_two_int_to_one(ssaframesize, Secs_size(secs)));

  //valid epcm of type secs and enclave address of 0, enclavesecs undefined thus set to 0
  //arg1: valid, arg2-4: rwx, arg5: page type, arg6: enclavesecs, arg7: enclaveaddress
  epcm[pageof_pa(pa)] := Epcm(true, false, false, false, pt_secs, k0_wap_addr_t, k0_vaddr_t);

  //set baseaddr and size from the input secs struct, initialized must be false, mrsigner is not yet set
  call unchecked_write_secs(pageof_pa(pa),             //writing to secs[pa]
                            Secs(Secs_baseaddr(secs),  //baseaddr (evrange base)
                            Secs_size(secs),           //size (evrange high - evrange base)
                            false,                     //initialized
                            measurement,               //value doesn't matter for this model
                            hash(dummy_signing_key),   //value doesn't matter for this model
                            0,                         //ISV product id
                            0,                         //ISV version number
                            Secs_attributes(secs)));   //Attributes
}

//la: pagetable[la] holds the secs page of this enclave
//secs: secs struct to populate
procedure {:inline 1} ecreate(la: vaddr_t, secs: secs_t) 
returns (result: sgx_api_result_t)
modifies epcm, mem_secs, mem_reg, mem_tcs, arbitrary_write_count;
{
  var pa: wap_addr_t;
  pa := page_table_map[la];

  if (pageof_va(la) != la) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (!page_table_valid[la]) { result := sgx_api_invalid_value; return;  }
  if (!is_epc_address(pa) || Epcm_valid(epcm[pageof_pa(pa)])) { result := sgx_api_invalid_value; return;  } //must be a free epc address
  if (Lp_state_cr_enclave_mode(lp_state[curr_lp])) { result := sgx_api_invalid_value; return;  } //enclave cannot call ecreate
  if (! (GT_va(Secs_size(secs), k0_vaddr_t)) ) { result := sgx_api_invalid_value; return;  } //positive sized enclave

  call ecreate_unchecked(la, secs);
  result := sgx_api_success;
}

//rcx: address of destination epc page
//rbx_linaddr: linear address with which one addresses this epc page
//rbx_secs: linear address of the SECS page
//d: data to write to the epc page
procedure {:inline 1} eadd_reg_unchecked(rbx_linaddr: vaddr_t, rbx_secs: vaddr_t, rcx: vaddr_t, r: bool, w: bool, x: bool, d: mem_t)
modifies epcm, mem_secs, mem_reg, mem_tcs, arbitrary_write_count;
{
  var epc_pa : wap_addr_t;
  var secs_pa : wap_addr_t;

  epc_pa := page_table_map[rcx];
  secs_pa := page_table_map[rbx_secs];
  epcm[pageof_pa(epc_pa)] := Epcm(true, r, w, x, pt_reg, secs_pa, pageof_va(rbx_linaddr));
  havoc mem_reg;
  assume (forall a: wap_addr_t :: ((LT_wapa(a, epc_pa) && GE_wapa(a, PLUS_wapa(epc_pa, 4096bv22))) ==> mem_reg[a] == old(mem_reg)[a]) &&
                                  ((GE_wapa(a, epc_pa) && LT_wapa(a, PLUS_wapa(epc_pa, 4096bv22))) ==> mem_reg[a] == d[a]));
  mem_secs[pageof_pa(epc_pa)]  := arbitrary_secs_val(arbitrary_write_count);
  mem_tcs[pageof_pa(epc_pa)]  := arbitrary_tcs_val(arbitrary_write_count);
  arbitrary_write_count := arbitrary_write_count + 1;
}

procedure {:inline 1} eadd_reg(rbx_linaddr: vaddr_t, rbx_secs: vaddr_t, rcx: vaddr_t, r: bool, w: bool, x: bool, d: mem_t)
returns (result: sgx_api_result_t)
modifies epcm, mem_secs, mem_reg, mem_tcs, arbitrary_write_count;
{
  var epc_pa : wap_addr_t;
  var secs_pa : wap_addr_t;

  epc_pa := page_table_map[rcx];
  secs_pa := page_table_map[rbx_secs];

  if (pageof_va(rcx) != rcx) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (pageof_va(rbx_secs) != rbx_secs) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (pageof_pa(epc_pa) != epc_pa) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (pageof_pa(secs_pa) != secs_pa) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (!page_table_valid[rcx]) { result := sgx_api_invalid_value; return;  }
  if (!page_table_valid[rbx_secs]) { result := sgx_api_invalid_value; return;  }
  if ( ! (is_epc_address(secs_pa) && 
          Epcm_valid(epcm[pageof_pa(secs_pa)]) && 
          Epcm_pt(epcm[pageof_pa(secs_pa)]) == pt_secs &&
          !Secs_initialized(mem_secs[secs_pa])) ) { result := sgx_api_invalid_value; return;  }
  if ( !(GE_va(rbx_linaddr, Secs_baseaddr(mem_secs[secs_pa])) &&
         LT_va(rbx_linaddr, PLUS_va(Secs_baseaddr(mem_secs[secs_pa]), Secs_size(mem_secs[secs_pa])))) ) { result := sgx_api_invalid_value; return; }
  if ( !(is_epc_address(epc_pa) && (!Epcm_valid(epcm[pageof_pa(epc_pa)]))) ) { result := sgx_api_invalid_value; return;  } //must be a free epc address
  if (Lp_state_cr_enclave_mode(lp_state[curr_lp])) { result := sgx_api_invalid_value; return;  } //enclave cannot call eadd

  call eadd_reg_unchecked(rbx_linaddr, rbx_secs, rcx, r, w, x, d);
  result := sgx_api_success;
}


procedure {:inline 1} eadd_tcs_unchecked(rbx_linaddr: vaddr_t, rbx_secs: vaddr_t, rcx: vaddr_t, r: bool, w: bool, x: bool, tcs: tcs_t)
modifies epcm, mem_secs, mem_reg, mem_tcs, arbitrary_write_count;
{
  var epc_pa : wap_addr_t;
  var secs_pa : wap_addr_t;

  epc_pa := page_table_map[rcx];
  secs_pa := page_table_map[rbx_secs];
  epcm[pageof_pa(epc_pa)] := Epcm(true, r, w, x, pt_tcs, secs_pa, pageof_va(rbx_linaddr));
  //active = false, interrupted = false, and cssa must be 0
  call unchecked_write_tcs(epc_pa, Tcs(false, false, Tcs_ossa(tcs), Tcs_nssa(tcs), k0_vaddr_t));
}

procedure {:inline 1} eadd_tcs(rbx_linaddr: vaddr_t, rbx_secs: vaddr_t, rcx: vaddr_t, r: bool, w: bool, x: bool, tcs: tcs_t)
returns (result: sgx_api_result_t)
modifies epcm, mem_secs, mem_reg, mem_tcs, arbitrary_write_count;
{
  var epc_pa : wap_addr_t;
  var secs_pa : wap_addr_t;

  epc_pa := page_table_map[rcx];
  secs_pa := page_table_map[rbx_secs];

  if (pageof_va(rcx) != rcx) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (pageof_va(rbx_secs) != rbx_secs) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (pageof_pa(epc_pa) != epc_pa) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (pageof_pa(secs_pa) != secs_pa) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (!page_table_valid[rcx]) { result := sgx_api_invalid_value; return;  }
  if (!page_table_valid[rbx_secs]) { result := sgx_api_invalid_value; return;  }
  if (! (is_epc_address(secs_pa) && 
         Epcm_valid(epcm[pageof_pa(secs_pa)]) && 
         Epcm_pt(epcm[pageof_pa(secs_pa)]) == pt_secs &&
         !Secs_initialized(mem_secs[secs_pa])) ) { result := sgx_api_invalid_value; return;  }
  if ( !(GE_va(rbx_linaddr, Secs_baseaddr(mem_secs[secs_pa])) &&
         LT_va(rbx_linaddr, PLUS_va(Secs_baseaddr(mem_secs[secs_pa]), Secs_size(mem_secs[secs_pa])))) ) { result := sgx_api_invalid_value; return; }
  if (! (is_epc_address(epc_pa) && !Epcm_valid(epcm[pageof_pa(epc_pa)])) ) { result := sgx_api_invalid_value; return;  } //must be a free epc address
  if (! (!Lp_state_cr_enclave_mode(lp_state[curr_lp])) ) { result := sgx_api_invalid_value; return;  } //enclave cannot call eadd
  if (! (GE_va(Tcs_ossa(tcs), k0_vaddr_t)) && (GE_va(Tcs_nssa(tcs), k0_vaddr_t)) ) { result := sgx_api_invalid_value; return;  }

  call eadd_tcs_unchecked(rbx_linaddr, rbx_secs, rcx, r, w, x, tcs);
  result := sgx_api_success;
}


// remove EPC page at EPC address la
procedure {:inline 1} eremove_unchecked(rcx: vaddr_t)
modifies epcm;
{
  var epc_pa: wap_addr_t;
  epc_pa := page_table_map[rcx];
  //set valid bit to false, which dummy_epcm has
  epcm[pageof_pa(epc_pa)] := dummy_epcm;
}

procedure {:inline 1} eremove(rcx: vaddr_t)
returns (result: sgx_api_result_t)
modifies epcm;
{
  var epc_pa : wap_addr_t;
  epc_pa := page_table_map[rcx];

  if (pageof_va(rcx) != rcx) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (pageof_pa(epc_pa) != epc_pa) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (!page_table_valid[rcx]) { result := sgx_api_invalid_value; return;  }
  if (! (is_epc_address(epc_pa)) ) { result := sgx_api_invalid_value; return;  }
  if (! ((Epcm_valid(epcm[pageof_pa(epc_pa)]) &&
           Epcm_pt(epcm[pageof_pa(epc_pa)]) == pt_secs) ==>
           no_pages_in_enclave(epcm, epc_pa)) ) { result := sgx_api_invalid_value; return;  }
  if (! ((Epcm_valid(epcm[pageof_pa(epc_pa)]) &&
           Epcm_pt(epcm[pageof_pa(epc_pa)]) != pt_secs) ==>
           no_threads_in_enclave(lp_state, Epcm_enclavesecs(epcm[pageof_pa(epc_pa)]))) ) { result := sgx_api_invalid_value; return;  }
  if (Lp_state_cr_enclave_mode(lp_state[curr_lp])) { result := sgx_api_invalid_value; return;  }

  call eremove_unchecked(rcx);
  result := sgx_api_success;
}

// take measurement of a 256 byte region, must be invokes 16 times to measure a page
// However, this model takes the entire measurement of the page at once
procedure {:inline 1} eextend_unchecked(rcx: vaddr_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs; 
{
  var secs : secs_t;
  var tmp_enclaveoffset : vaddr_t;
  var tmp_mrenclave : sgx_measurement_t;
  var epc_pa : wap_addr_t;

  epc_pa := page_table_map[rcx];
  secs := mem_secs[Epcm_enclavesecs(epcm[pageof_pa(epc_pa)])];

  tmp_enclaveoffset := MINUS_va(Epcm_enclaveaddress(epcm[pageof_pa(epc_pa)]), Secs_baseaddr(secs));
  tmp_enclaveoffset := PLUS_va(tmp_enclaveoffset, (0bv20 ++ rcx[12:0]));
  
  tmp_mrenclave := Secs_mrenclave(secs);
  tmp_mrenclave := sha256update(tmp_mrenclave, vaddr_to_int(tmp_enclaveoffset));
  if (Epcm_pt(epcm[pageof_pa(epc_pa)]) == pt_reg) {
    tmp_mrenclave := sha256update(tmp_mrenclave, reg_to_int(mem_reg[epc_pa])); 
  } else {
    tmp_mrenclave := sha256update(tmp_mrenclave, tcs_to_int(mem_tcs[epc_pa])); 
  }

  call unchecked_write_secs(Epcm_enclavesecs(epcm[pageof_pa(epc_pa)]),
                            Secs(Secs_baseaddr(secs), Secs_size(secs), Secs_initialized(secs), 
                            tmp_mrenclave, Secs_mrsigner(secs), 
                            Secs_isvprodid(secs), Secs_isvsvn(secs), Secs_attributes(secs)));
}

procedure {:inline 1} eextend(rcx: vaddr_t)
returns (result: sgx_api_result_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs; 
{
  var epc_pa : wap_addr_t;
  epc_pa := page_table_map[rcx];

  if (!page_table_valid[rcx]) { result := sgx_api_invalid_value; return;  }
  if (! (is_epc_address(epc_pa)) ) { result := sgx_api_invalid_value; return;  }
  if (! (Epcm_valid(epcm[pageof_pa(epc_pa)]) &&
         (Epcm_pt(epcm[pageof_pa(epc_pa)]) == pt_reg ||
          Epcm_pt(epcm[pageof_pa(epc_pa)]) == pt_tcs)) ) { result := sgx_api_invalid_value; return;  }
  if (Secs_initialized(mem_secs[Epcm_enclavesecs(epcm[pageof_pa(epc_pa)])])) { result := sgx_api_invalid_value; return;  }
  if (Lp_state_cr_enclave_mode(lp_state[curr_lp])) { result := sgx_api_invalid_value; return;  }

  call eextend_unchecked(rcx);
  result := sgx_api_success;
}

//rbx: targetinfo struct, rcx: reportdata struct, rdx: addr containing output report struct
procedure {:inline 1} ereport_unchecked(targetinfo: targetinfo_t, reportdata: word_t)
returns (report_maced: report_maced_t)
{
  var tmp_reportkey : key_t; 
  var tmp_currentsecs : secs_t;
  var report : report_t;
  var tmp_report_mac : mactext_t report_t;

  tmp_reportkey := derive_key_ereport(Targetinfo_attributes(targetinfo),
                                      Targetinfo_measurement(targetinfo));
  tmp_currentsecs := mem_secs[Lp_state_cr_active_secs(lp_state[curr_lp])];
  report := Report(Secs_isvprodid(tmp_currentsecs),
                   Secs_isvsvn(tmp_currentsecs),
                   Secs_attributes(tmp_currentsecs),
                   reportdata,
                   Secs_mrenclave(tmp_currentsecs),
                   Secs_mrsigner(tmp_currentsecs));
                   
  tmp_report_mac := cmac(tmp_reportkey, report);
  report_maced := Report_maced(report, tmp_report_mac); 
}

procedure {:inline 1} ereport(targetinfo: targetinfo_t, reportdata: word_t)
returns (report_maced: report_maced_t, result: sgx_api_result_t)
{
  if (! (Lp_state_cr_enclave_mode(lp_state[curr_lp]))) { result := sgx_api_invalid_value; return;  } 
  call report_maced := ereport_unchecked(targetinfo, reportdata);
  result := sgx_api_success;
}

// initialize enclave whose SECS page is located at EPC address ls
//rbx -> sigstruct, rcx -> secs, rdx -> einittoken
procedure {:inline 1} einit_unchecked(sigstruct_signed: sigstruct_signed_t, rcx: vaddr_t, einittoken: einittoken_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs; 
{
  var secs : secs_t;
  var tmp_mrsigner : hashtext_t key_t;
  var sigstruct : sigstruct_t;
  var secs_pa : wap_addr_t;

  secs_pa := page_table_map[rcx];

  sigstruct := Sigstruct_signed_sigstruct(sigstruct_signed);
  tmp_mrsigner := hash(Sigstruct_modulus(sigstruct)); 
  
  secs := mem_secs[secs_pa];

  call unchecked_write_secs(secs_pa,
                            Secs(Secs_baseaddr(secs), Secs_size(secs), true, 
                                 Secs_mrenclave(secs), tmp_mrsigner, 
                                 Sigstruct_isvprodid(sigstruct), Sigstruct_isvsvn(sigstruct),
                                 Secs_attributes(secs)));
}

procedure {:inline 1} einit(sigstruct_signed: sigstruct_signed_t, rcx: vaddr_t, einittoken: einittoken_t)
returns (result: sgx_api_result_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs; 
{
  var secs_pa : wap_addr_t;
  secs_pa := page_table_map[rcx];

  if (pageof_va(rcx) != rcx) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (pageof_pa(secs_pa) != secs_pa) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (!page_table_valid[rcx]) { result := sgx_api_invalid_value; return;  }
  if (! (Epcm_valid(epcm[pageof_pa(secs_pa)]) && Epcm_pt(epcm[pageof_pa(secs_pa)]) == pt_secs) ) { result := sgx_api_invalid_value; return;  } 
  if (! (is_epc_address(secs_pa) && !Secs_initialized(mem_secs[secs_pa])) ) { result := sgx_api_invalid_value; return;  }
  if (Lp_state_cr_enclave_mode(lp_state[curr_lp])) { result := sgx_api_invalid_value; return;  } //enclave cannot call einit

  //assume decrypt(Sigstruct_modulus(Sigstruct_signed_sigstruct(sigstruct_signed)), 
  //               Sigstruct_signed_signature(sigstruct_signed)) == 
   //      hash(Sigstruct_signed_sigstruct(sigstruct_signed)); 
  //assume Sigstruct_enclavehash(Sigstruct_signed_sigstruct(sigstruct_signed)) == Secs_mrenclave(mem_secs[page_table_map[ls]]);
  //assume Attributes_einittokenkey(Secs_attributes(mem_secs[page_table_map[ls]])) ==> 
  //       (hash(Sigstruct_modulus(Sigstruct_signed_sigstruct(sigstruct_signed))) == CSR_INTELPUBKEYHASH);
  //assume Secs_attributes(mem_secs[secs_pa]) == Sigstruct_attributes(Sigstruct_signed_sigstruct(sigstruct_signed));
  //assume (!Einittoken_valid(einittoken)) ==> (hash(Sigstruct_modulus(Sigstruct_signed_sigstruct(sigstruct_signed))) == CSR_INTELPUBKEYHASH);
  //assume (Einittoken_valid(einittoken)) ==>
  //       (Einittoken_mrenclave(einittoken) == Secs_mrenclave(mem_secs[page_table_map[ls]]) &&
  //        Einittoken_mrsigner(einittoken) == hash(Sigstruct_modulus(Sigstruct_signed_sigstruct(sigstruct_signed))));
  //assume (Einittoken_valid(einittoken)) ==> (Secs_attributes(mem_secs[secs_pa]) == Einittoken_attributes(einittoken));

  call einit_unchecked(sigstruct_signed, rcx, einittoken);
  result := sgx_api_success;  
}


//Enter an enclave via a thread whose TCS lives at EPC address la
procedure {:inline 1} eenter_unchecked(rbx: vaddr_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs, lp_state; 
{
  var tcs_pa: wap_addr_t;
  var secs_pa: wap_addr_t;
  var pcssa: wap_addr_t;

  tcs_pa := page_table_map[rbx];
  secs_pa := Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)]);
  pcssa := page_table_map[cssa_addr(mem_secs[Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)])], mem_tcs[tcs_pa])]; 

  call unchecked_write_tcs(tcs_pa, Tcs(true,
                                   Tcs_interrupted(mem_tcs[tcs_pa]),
                                   Tcs_ossa(mem_tcs[tcs_pa]),
                                   Tcs_nssa(mem_tcs[tcs_pa]),
                                   Tcs_cssa(mem_tcs[tcs_pa])
                                  ));

  //Lp_state(cr_enclave_mode: bool, cr_tcs_pa: wap_addr_t, cr_active_secs: wap_addr_t, cr_elrange: lr_register_t, ssa_pa: wap_addr_t)
  lp_state[curr_lp] := Lp_state(true,    //cr_enclave_mode 
                                tcs_pa,  //TCS pa 
                                secs_pa, //SECS pa 
                                Lr_register(Secs_baseaddr(mem_secs[secs_pa]), Secs_size(mem_secs[secs_pa])), //evrange base and size 
                                pcssa
                               ); 
}

procedure {:inline 1} eenter(rbx: vaddr_t)
returns (result: sgx_api_result_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs, lp_state; 
{
  var tcs_pa: wap_addr_t;
  tcs_pa := page_table_map[rbx];

  if (pageof_va(rbx) != rbx) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (pageof_pa(tcs_pa) != tcs_pa) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (!page_table_valid[rbx]) { result := sgx_api_invalid_value; return;  }
  if (!is_epc_address(tcs_pa)) { result := sgx_api_invalid_value; return;  }
  if (! (!Tcs_active(mem_tcs[tcs_pa]) && !Tcs_interrupted(mem_tcs[tcs_pa])) ) { result := sgx_api_invalid_value; return;  }
  if (! (Epcm_enclaveaddress(epcm[pageof_pa(tcs_pa)]) == rbx && Epcm_pt(epcm[pageof_pa(tcs_pa)]) == pt_tcs && Epcm_valid(epcm[pageof_pa(tcs_pa)])) ) { result := sgx_api_invalid_value; return;  }
  if (! (LT_va(Tcs_cssa(mem_tcs[tcs_pa]), Tcs_nssa(mem_tcs[tcs_pa])) &&
         is_epc_address(page_table_map[cssa_addr(mem_secs[Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)])], mem_tcs[tcs_pa])]) && 
         Epcm_valid(epcm[pageof_pa(page_table_map[cssa_addr(mem_secs[Epcm_enclavesecs(epcm[tcs_pa])], mem_tcs[tcs_pa])])]) && 
         Epcm_pt(epcm[pageof_pa(page_table_map[cssa_addr(mem_secs[Epcm_enclavesecs(epcm[tcs_pa])], mem_tcs[tcs_pa])])]) == pt_reg &&
         Epcm_enclaveaddress(epcm[pageof_pa(page_table_map[cssa_addr(mem_secs[Epcm_enclavesecs(epcm[tcs_pa])], mem_tcs[tcs_pa])])]) == cssa_addr(mem_secs[Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)])], mem_tcs[tcs_pa]) &&
         Epcm_enclavesecs(epcm[pageof_pa(page_table_map[cssa_addr(mem_secs[Epcm_enclavesecs(epcm[tcs_pa])], mem_tcs[tcs_pa])])]) == Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)]) && 
         Secs_initialized(mem_secs[Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)])])) ) { result := sgx_api_invalid_value; return;  }
  if (Lp_state_cr_enclave_mode(lp_state[curr_lp])) { result := sgx_api_invalid_value; return;  }

  call eenter_unchecked(rbx);
  result := sgx_api_success;
}

//Resume an enclave via a thread whose TCS lives at la
procedure {:inline 1} eresume_unchecked(rbx: vaddr_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs, lp_state, xstate; 
{
  var tcs_pa: wap_addr_t;
  var secs_pa: wap_addr_t;
  var ppssa: wap_addr_t;

  tcs_pa := page_table_map[rbx];
  secs_pa := Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)]);
  ppssa := page_table_map[pssa_addr(mem_secs[Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)])], mem_tcs[tcs_pa])]; 

  call unchecked_write_tcs(tcs_pa, Tcs(true,  //active
                                    false, //interrupted
                                    Tcs_ossa(mem_tcs[tcs_pa]),
                                    Tcs_nssa(mem_tcs[tcs_pa]),
                                    MINUS_va(Tcs_cssa(mem_tcs[tcs_pa]), k1_vaddr_t)));

  lp_state[curr_lp] := Lp_state(true, 
                                tcs_pa,
                                secs_pa,
                                Lr_register(Secs_baseaddr(mem_secs[secs_pa]), Secs_size(mem_secs[secs_pa])),
                                ppssa
                               );
  xstate[curr_lp] := word_to_xstate(mem_reg[ppssa]); 
}

procedure {:inline 1} eresume(rbx: vaddr_t)
returns (result: sgx_api_result_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs, lp_state, xstate; 
{
  var tcs_pa: wap_addr_t;
  tcs_pa := page_table_map[rbx];

  if (pageof_va(rbx) != rbx) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (pageof_pa(tcs_pa) != tcs_pa) { result := sgx_api_invalid_value; return; } //la must be aligned
  if (!page_table_valid[rbx]) { result := sgx_api_invalid_value; return;  }
  if (Tcs_active(mem_tcs[tcs_pa])) { result := sgx_api_invalid_value; return;  } 
  if (!is_epc_address(tcs_pa)) { result := sgx_api_invalid_value; return;  }
  if (! (Epcm_valid(epcm[pageof_pa(tcs_pa)])) ) { result := sgx_api_invalid_value; return;  }
  if (! (Epcm_enclaveaddress(epcm[pageof_pa(tcs_pa)]) == rbx) && (Epcm_pt(epcm[pageof_pa(tcs_pa)]) == pt_tcs) ) { result := sgx_api_invalid_value; return;  }
  if (! (GT_va(Tcs_cssa(mem_tcs[tcs_pa]), k0_vaddr_t)) ) { result := sgx_api_invalid_value; return;  }
  if (! (is_epc_address(page_table_map[pssa_addr(mem_secs[Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)])], mem_tcs[tcs_pa])]) && 
         Epcm_valid(epcm[pageof_pa(page_table_map[pssa_addr(mem_secs[Epcm_enclavesecs(epcm[tcs_pa])], mem_tcs[tcs_pa])])]) && 
         Epcm_pt(epcm[pageof_pa(page_table_map[pssa_addr(mem_secs[Epcm_enclavesecs(epcm[tcs_pa])], mem_tcs[tcs_pa])])]) == pt_reg) ) { }
  if (! (Epcm_enclaveaddress(epcm[pageof_pa(page_table_map[pssa_addr(mem_secs[Epcm_enclavesecs(epcm[tcs_pa])], mem_tcs[tcs_pa])])]) == 
                                             pssa_addr(mem_secs[Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)])], mem_tcs[tcs_pa])) ) { result := sgx_api_invalid_value; return;  }
  if (! (Epcm_enclavesecs(epcm[pageof_pa(page_table_map[pssa_addr(mem_secs[Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)])], mem_tcs[tcs_pa])])]) == 
         Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)])) ) { result := sgx_api_invalid_value; return;  }
  if (! (Secs_initialized(mem_secs[Epcm_enclavesecs(epcm[pageof_pa(tcs_pa)])])) ) { result := sgx_api_invalid_value; return;  }
  if (Lp_state_cr_enclave_mode(lp_state[curr_lp])) { result := sgx_api_invalid_value; return;  }

  call eresume_unchecked(rbx);
  result := sgx_api_success;
}

function AES_GCM_ENC_reg(plaintext: word_t) : word_t;
function AES_GCM_DEC_reg(ciphertext: word_t) : word_t;
axiom (forall ptxt: word_t, ctxt: word_t :: {AES_GCM_ENC_reg(ptxt), AES_GCM_DEC_reg(ctxt)}
              AES_GCM_ENC_reg(ptxt) == ctxt ==> AES_GCM_DEC_reg(ctxt) == ptxt); 
axiom (forall ptxt: word_t, ctxt: word_t :: {AES_GCM_ENC_reg(ptxt), AES_GCM_DEC_reg(ctxt)}
              AES_GCM_DEC_reg(ctxt) == ptxt ==> AES_GCM_ENC_reg(ptxt) == ctxt); 

function AES_GCM_ENC_tcs(plaintext: tcs_t) : word_t;
function AES_GCM_DEC_tcs(ciphertext: word_t) : tcs_t;
axiom (forall ptxt: tcs_t, ctxt: word_t :: {AES_GCM_ENC_tcs(ptxt), AES_GCM_DEC_tcs(ctxt)}
              AES_GCM_ENC_tcs(ptxt) == ctxt ==> AES_GCM_DEC_tcs(ctxt) == ptxt); 
axiom (forall ptxt: tcs_t, ctxt: word_t :: {AES_GCM_ENC_tcs(ptxt), AES_GCM_DEC_tcs(ctxt)}
              AES_GCM_DEC_tcs(ctxt) == ptxt ==> AES_GCM_ENC_tcs(ptxt) == ctxt); 

function AES_GCM_ENC_secs(plaintext: secs_t) : word_t;
function AES_GCM_DEC_secs(ciphertext: word_t) : secs_t;
axiom (forall ptxt: secs_t, ctxt: word_t :: {AES_GCM_ENC_secs(ptxt), AES_GCM_DEC_secs(ctxt)}
              AES_GCM_ENC_secs(ptxt) == ctxt ==> AES_GCM_DEC_secs(ctxt) == ptxt); 
axiom (forall ptxt: secs_t, ctxt: word_t :: {AES_GCM_ENC_secs(ptxt), AES_GCM_DEC_secs(ctxt)}
              AES_GCM_DEC_secs(ctxt) == ptxt ==> AES_GCM_ENC_secs(ptxt) == ctxt); 


//copy a page from EPC page la to dst_la in unprotected memory
procedure {:inline 1} ewb(la: vaddr_t, pageinfo: pageinfo_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs, epcm; 
requires (!Lp_state_cr_enclave_mode(lp_state[curr_lp])); //only OS/VMM allowed to call ewb
requires (is_epc_address(page_table_map[la]) && Epcm_valid(epcm[page_table_map[la]]));
//FIXME: This is too strict, but PRM is unclear on the requirements
requires ((Epcm_pt(epcm[page_table_map[la]]) == pt_reg) || 
          (Epcm_pt(epcm[page_table_map[la]]) == pt_tcs)) ==>
          no_threads_in_enclave(lp_state, Epcm_enclavesecs(epcm[page_table_map[la]]));
//FIXME: This is too strict, but PRM is unclear on the requirements
requires (Epcm_pt(epcm[page_table_map[la]]) == pt_secs) ==> 
         (no_threads_in_enclave(lp_state, page_table_map[la]) &&
          no_pages_in_enclave(epcm, page_table_map[la]));
requires (!is_epc_address(page_table_map[Pageinfo_srcpge(pageinfo)]));
{
  var pa: wap_addr_t;
  var tmp_srcpge : vaddr_t;

  pa := page_table_map[la];
  tmp_srcpge := Pageinfo_srcpge(pageinfo);

  if (Epcm_pt(epcm[pa]) == pt_reg) {
    call unchecked_write_reg(page_table_map[tmp_srcpge], AES_GCM_ENC_reg(mem_reg[pa]));
  } else if (Epcm_pt(epcm[pa]) == pt_tcs) {
    call unchecked_write_reg(page_table_map[tmp_srcpge], AES_GCM_ENC_tcs(mem_tcs[pa]));
  } else if (Epcm_pt(epcm[pa]) == pt_secs) {
    call unchecked_write_reg(page_table_map[tmp_srcpge], AES_GCM_ENC_secs(mem_secs[pa]));
  }

  //epcm[pa] := Epcm(false, Epcm_pt(epcm[pa]), Epcm_enclavesecs(epcm[pa]), Epcm_enclaveaddress(epcm[pa])); 
  epcm[pa] := dummy_epcm;
  //write out pcmd
}

//copy a page from src_la to EPC page la
procedure {:inline 1} eldu(la: vaddr_t, pageinfo: pageinfo_t)
modifies mem_reg, mem_tcs, mem_secs, epcm, arbitrary_write_count;
requires (is_epc_address(page_table_map[la]) && !Epcm_valid(epcm[page_table_map[la]]));
requires ((Secinfo_flags_pt(Pageinfo_secinfo(pageinfo)) == pt_reg) || 
          (Secinfo_flags_pt(Pageinfo_secinfo(pageinfo)) == pt_tcs)) ==>
          (is_epc_address(Pageinfo_secs(pageinfo)) &&
           Epcm_valid(epcm[Pageinfo_secs(pageinfo)]) &&
           Epcm_pt(epcm[Pageinfo_secs(pageinfo)]) == pt_secs);
requires (Secinfo_flags_pt(Pageinfo_secinfo(pageinfo)) == pt_secs) ==> 
         (Pageinfo_secs(pageinfo) == k0_wap_addr_t);
{
  var tmp_srcpge : vaddr_t;
  var tmp_secs : wap_addr_t;
  var tmp_secinfo : secinfo_t; 
  var pa: wap_addr_t;
  var tmp_header_secinfo_flags_pt : page_t; 

  pa := page_table_map[la];
  tmp_srcpge := Pageinfo_srcpge(pageinfo);
  tmp_secs := Pageinfo_secs(pageinfo);
  tmp_secinfo := Pageinfo_secinfo(pageinfo);

  tmp_header_secinfo_flags_pt := Secinfo_flags_pt(tmp_secinfo); 
  if (tmp_header_secinfo_flags_pt == pt_reg) {
    call unchecked_write_reg(pa, AES_GCM_DEC_reg(mem_reg[page_table_map[tmp_srcpge]]));
  } else if (tmp_header_secinfo_flags_pt == pt_tcs) {
    call unchecked_write_tcs(pa, AES_GCM_DEC_tcs(mem_reg[page_table_map[tmp_srcpge]]));
  } else if (tmp_header_secinfo_flags_pt == pt_secs) {
    call unchecked_write_secs(pa, AES_GCM_DEC_secs(mem_reg[page_table_map[tmp_srcpge]]));
  }

  epcm[pa] := Epcm(true, true, true, true,
                   tmp_header_secinfo_flags_pt, 
                   Pageinfo_secs(pageinfo), 
                   Pageinfo_linaddr(pageinfo)); 
}

procedure {:inline 1} eexit()
returns (result: sgx_api_result_t)
modifies mem_reg, xstate, lp_state, mem_tcs, mem_secs, arbitrary_write_count;
{
  var ptcs  : wap_addr_t;
  if (! (Lp_state_cr_enclave_mode(lp_state[curr_lp])) ) { result := sgx_api_invalid_value; return; }

  ptcs := Lp_state_cr_tcs_pa(lp_state[curr_lp]);

  lp_state[curr_lp] := Lp_state(false,
                                Lp_state_cr_tcs_pa(lp_state[curr_lp]),
                                Lp_state_cr_active_secs(lp_state[curr_lp]),
                                Lp_state_cr_elrange(lp_state[curr_lp]),
                                Lp_state_ssa_pa(lp_state[curr_lp])
                               ); 

  call unchecked_write_tcs(ptcs, Tcs(false,
                                     Tcs_interrupted(mem_tcs[ptcs]),
                                     Tcs_ossa(mem_tcs[ptcs]),
                                     Tcs_nssa(mem_tcs[ptcs]),
                                     Tcs_cssa(mem_tcs[ptcs])
                                 ));
  result := sgx_api_success;
}

procedure {:inline 1} aexit(interrupt: bool)
returns (result: sgx_api_result_t)
modifies mem_reg, xstate, lp_state, mem_tcs, mem_secs, arbitrary_write_count;
{
  var pt : wap_addr_t;
  var pc : wap_addr_t;

  if (! (Lp_state_cr_enclave_mode(lp_state[curr_lp])) ) { result := sgx_api_invalid_value; return; }

  pt := Lp_state_cr_tcs_pa(lp_state[curr_lp]);
  pc := Lp_state_ssa_pa(lp_state[curr_lp]);

  call unchecked_write_reg(pc, xstate_to_word(xstate[curr_lp]));
  xstate[curr_lp] := dummy_xstate;
  lp_state[curr_lp] := Lp_state(false,
                                Lp_state_cr_tcs_pa(lp_state[curr_lp]),
                                Lp_state_cr_active_secs(lp_state[curr_lp]),
                                Lp_state_cr_elrange(lp_state[curr_lp]),
                                Lp_state_ssa_pa(lp_state[curr_lp])
                               ); 
  call unchecked_write_tcs(pt, Tcs(false,
                                   interrupt,
                                   Tcs_ossa(mem_tcs[pt]),
                                   Tcs_nssa(mem_tcs[pt]),
                                   PLUS_va(Tcs_cssa(mem_tcs[pt]), k1_vaddr_t)
                                  ));

  result := sgx_api_success;
}

procedure {:inline 1} interrupt()
returns (result: sgx_api_result_t)
modifies mem_reg, xstate, lp_state, mem_tcs, mem_secs, arbitrary_write_count;
{
  if (Lp_state_cr_enclave_mode(lp_state[curr_lp])) {
    call result := aexit(true);  
  }
}

procedure {:inline 1} exception()
returns (result: sgx_api_result_t)
modifies mem_reg, xstate, lp_state, mem_tcs, mem_secs, arbitrary_write_count;
{
  if (Lp_state_cr_enclave_mode(lp_state[curr_lp])) {
    call result := aexit(false);  
  }
}

//rbx: input keyrequest struct, rcx: output outputdata struct
//return sealing and attestation keys
procedure {:inline 1} egetkey(keyrequest: keyrequest_t) returns (result: key_t)
requires (Lp_state_cr_enclave_mode(lp_state[curr_lp])); 
requires (Keyrequest_keyname(keyrequest) == seal_key) ==>
         (Keyrequest_isvsvn(keyrequest) > Secs_isvsvn(mem_secs[Lp_state_cr_active_secs(lp_state[curr_lp])]));
requires Keyrequest_keyname(keyrequest) == seal_key ||
         Keyrequest_keyname(keyrequest) == report_key;
{
  var tmp_currentsecs : secs_t;
  var keyname : keyname_t;
  var tmp_mrenclave : sgx_measurement_t;
  var tmp_mrsigner : hashtext_t key_t;
  tmp_currentsecs := mem_secs[Lp_state_cr_active_secs(lp_state[curr_lp])];
  keyname := Keyrequest_keyname(keyrequest);

  if (keyname == seal_key) {
    tmp_mrenclave := 0;
    //include enclave identity?
    if (Keyrequest_keypolicy_mrenclave(keyrequest)) {
      tmp_mrenclave := Secs_mrenclave(tmp_currentsecs);
    }
    tmp_mrsigner := hash(dummy_signing_key);
    //include enclave author?
    if (Keyrequest_keypolicy_mrsigner(keyrequest)) {
      tmp_mrsigner := Secs_mrsigner(tmp_currentsecs);
    }
    result := derive_key_egetkey(seal_key, 
                                 Secs_isvprodid(tmp_currentsecs),
                                 Keyrequest_isvsvn(keyrequest),
                                 Secs_attributes(tmp_currentsecs),
                                 tmp_mrenclave, 
                                 tmp_mrsigner);
  }
  else if(keyname == report_key) {
    result := derive_key_egetkey(report_key, 
                                0,
                                0,
                                Secs_attributes(tmp_currentsecs),
                                Secs_mrenclave(tmp_currentsecs), 
                                hash(dummy_signing_key));
  }
}


procedure {:inline 1} egetkey_with_assumptions(keyrequest: keyrequest_t) returns (result: key_t)
{
  assume (Lp_state_cr_enclave_mode(lp_state[curr_lp])); 
  assume (Keyrequest_keyname(keyrequest) == seal_key) ==>
         (Keyrequest_isvsvn(keyrequest) > Secs_isvsvn(mem_secs[Lp_state_cr_active_secs(lp_state[curr_lp])]));
  assume Keyrequest_keyname(keyrequest) == seal_key ||
         Keyrequest_keyname(keyrequest) == report_key;
  call result := egetkey(keyrequest);
}

//********************* All other operations *************************

procedure {:inline 1} sgx_store(la: vaddr_t, d: word_t)
returns (result: sgx_api_result_t)
modifies arbitrary_write_count, mem_reg, mem_secs, mem_tcs; 
{
  var is_writeable : bool;
  var pa : wap_addr_t;

  //FIXME: Model rwx permissions
  call is_writeable := is_accessible(curr_lp, la); 
  if (!is_writeable) { result := sgx_api_invalid_value; return; }

  call pa := translate(la); 
  if (pa == abort_page) { result := sgx_api_invalid_value; return; }

  call unchecked_write_reg(pa, d);
  result := sgx_api_success;
}

procedure {:inline 1} sgx_load(la: vaddr_t)
returns (d: word_t, result: sgx_api_result_t)
{
  var is_readable : bool;
  var pa : wap_addr_t;

  //FIXME: Model rwx permissions
  call is_readable := is_accessible(curr_lp, la); 
  if (!is_readable) { result := sgx_api_invalid_value; return; }

  call pa := translate(la); 
  if (pa == abort_page) { result := sgx_api_invalid_value; return; }

  d := mem_reg[pa];
  result := sgx_api_success;
}

procedure {:inline 1} switch_thread (lp : lp_id_t)
modifies curr_lp;
{
  curr_lp := lp;
}

//Abstract computation
procedure {:inline 1} compute()
modifies xstate;
{
  var x: xstate_t;
  xstate[curr_lp] := x;
}

//Adversary update to page tables
procedure {:inline 1} update_page_table_map(l: vaddr_t, p: wap_addr_t)
modifies page_table_map;
{
  page_table_map[l] := p;
}

//********************* Properties *********************
function secs_valid(epcm : [wap_addr_t] epcm_entry_t, mem_secs : [wap_addr_t] secs_t) : bool; 
axiom (forall epcm : [wap_addr_t] epcm_entry_t, mem_secs : [wap_addr_t] secs_t ::
       {secs_valid(epcm, mem_secs)}
       secs_valid(epcm, mem_secs) <==> (forall pa : wap_addr_t ::
                                        (is_epc_address(pa) && Epcm_valid(epcm[pageof_pa(pa)]) && Epcm_pt(epcm[pageof_pa(pa)]) != pt_secs) ==> 
                                        (is_epc_address(Epcm_enclavesecs(epcm[pageof_pa(pa)])) && 
                                         Epcm_valid(epcm[Epcm_enclavesecs(epcm[pageof_pa(pa)])]) && 
                                         Epcm_pt(epcm[Epcm_enclavesecs(epcm[pageof_pa(pa)])]) == pt_secs)
                                       )); 

function lp_secs_inv(lp_state: [lp_id_t] lp_state_t, epcm : [wap_addr_t] epcm_entry_t) : bool;
axiom (forall lp_state : [lp_id_t] lp_state_t, epcm : [wap_addr_t] epcm_entry_t :: 
      {lp_secs_inv(lp_state, epcm)}
      lp_secs_inv(lp_state, epcm) <==> (forall lp: lp_id_t ::
                                       (Lp_state_cr_enclave_mode(lp_state[lp]) ==>
                                        Lp_state_cr_active_secs(lp_state[lp]) == 
                                        Epcm_enclavesecs(epcm[Lp_state_cr_tcs_pa(lp_state[lp])]))));

function lp_tcs_valid(lp_state: [lp_id_t] lp_state_t, epcm : [wap_addr_t] epcm_entry_t, mem_tcs : [wap_addr_t] tcs_t) : bool;
axiom (forall lp_state : [lp_id_t] lp_state_t, epcm : [wap_addr_t] epcm_entry_t, mem_tcs : [wap_addr_t] tcs_t :: 
      {lp_tcs_valid(lp_state, epcm, mem_tcs)}
      lp_tcs_valid(lp_state, epcm, mem_tcs) <==> (forall lp: lp_id_t ::
                                                 (Lp_state_cr_enclave_mode(lp_state[lp]) ==>
                                                 (is_epc_address(Lp_state_cr_tcs_pa(lp_state[lp])) &&
                                                  Epcm_valid(epcm[Lp_state_cr_tcs_pa(lp_state[lp])]) &&
                                                  Epcm_pt(epcm[Lp_state_cr_tcs_pa(lp_state[lp])]) == pt_tcs &&
                                                  Tcs_active(mem_tcs[Lp_state_cr_tcs_pa(lp_state[lp])]))
                                                  )));
 
