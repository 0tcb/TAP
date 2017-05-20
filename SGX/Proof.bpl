
procedure interrupted_enclave_unaffected_proof()
modifies mem_reg, mem_tcs, mem_secs, epcm, lp_state, xstate, page_table, curr_lp, arbitrary_write_count;
{
  var aux: bool; var aux_next: bool; var aux_next_next: bool; var aux_next_next_next: bool;
  var aux_const: bool; var aux_next_const: bool; var aux_next_next_const: bool; var aux_next_next_next_const: bool;
  var interrupted_thread: linear_address;

  //variable declarations
  var mem_reg1: [physical_address] data; var mem_reg2: [physical_address] data;
  var mem_secs1: [physical_address] secs_ty; var mem_secs2: [physical_address] secs_ty;
  var mem_tcs1: [physical_address] tcs_ty; var mem_tcs2: [physical_address] tcs_ty;
  var epcm1 : [physical_address] epcm_entry_ty; var epcm2 : [physical_address] epcm_entry_ty;
  var lp_state1 : [lp_id] lp_state_ty; var lp_state2 : [lp_id] lp_state_ty;
  var xstate1 : [lp_id] xstate_ty; var xstate2 : [lp_id] xstate_ty;
  var page_table1 : page_table_ty; var page_table2 : page_table_ty;
  var next_mem_reg1: [physical_address] data; var next_mem_reg2: [physical_address] data;
  var next_mem_secs1: [physical_address] secs_ty; var next_mem_secs2: [physical_address] secs_ty;
  var next_mem_tcs1: [physical_address] tcs_ty; var next_mem_tcs2: [physical_address] tcs_ty;
  var next_epcm1 : [physical_address] epcm_entry_ty; var next_epcm2 : [physical_address] epcm_entry_ty;
  var next_lp_state1 : [lp_id] lp_state_ty; var next_lp_state2 : [lp_id] lp_state_ty;
  var next_xstate1 : [lp_id] xstate_ty; var next_xstate2 : [lp_id] xstate_ty;
  var next_page_table1 : page_table_ty; var next_page_table2 : page_table_ty;

  var next_next_mem_reg1: [physical_address] data; var next_next_mem_reg2: [physical_address] data;
  var next_next_mem_secs1: [physical_address] secs_ty; var next_next_mem_secs2: [physical_address] secs_ty;
  var next_next_mem_tcs1: [physical_address] tcs_ty; var next_next_mem_tcs2: [physical_address] tcs_ty;
  var next_next_epcm1 : [physical_address] epcm_entry_ty; var next_next_epcm2 : [physical_address] epcm_entry_ty;
  var next_next_lp_state1 : [lp_id] lp_state_ty; var next_next_lp_state2 : [lp_id] lp_state_ty;
  var next_next_xstate1 : [lp_id] xstate_ty; var next_next_xstate2 : [lp_id] xstate_ty;
  var next_next_page_table1 : page_table_ty; var next_next_page_table2 : page_table_ty;

  var next_next_next_mem_reg1: [physical_address] data; var next_next_next_mem_reg2: [physical_address] data;
  var next_next_next_mem_secs1: [physical_address] secs_ty; var next_next_next_mem_secs2: [physical_address] secs_ty;
  var next_next_next_mem_tcs1: [physical_address] tcs_ty; var next_next_next_mem_tcs2: [physical_address] tcs_ty;
  var next_next_next_epcm1 : [physical_address] epcm_entry_ty; var next_next_next_epcm2 : [physical_address] epcm_entry_ty;
  var next_next_next_lp_state1 : [lp_id] lp_state_ty; var next_next_next_lp_state2 : [lp_id] lp_state_ty;
  var next_next_next_xstate1 : [lp_id] xstate_ty; var next_next_next_xstate2 : [lp_id] xstate_ty;
  var next_next_next_page_table1 : page_table_ty; var next_next_next_page_table2 : page_table_ty;

  var targetinfo: targetinfo_ty; var targetinfo_next: targetinfo_ty;
  var reportdata: data; var reportdata_next: data;


  var secs : secs_ty;
  var tcs : tcs_ty;
  var signing_key : key_ty;
  var desired_measurement : measurement_ty;
  var secret1: data;
  var attributes: attributes_ty;
  var signature : ciphertext_ty (hashtext_ty sigstruct_ty);
  var sigstruct: sigstruct_ty;
  var sigstruct_signed: sigstruct_signed_ty;
  var einittoken: einittoken_ty;

  var golden_secs : secs_ty;
  var golden_tcs : tcs_ty;
  var golden_reg : data;
  var golden_lpstate : lp_state_ty;
  var golden_epcm_2000 : epcm_entry_ty;
  var golden_epcm_2001 : epcm_entry_ty;
  var golden_epcm_2002 : epcm_entry_ty;
  var golden_epcm_2003 : epcm_entry_ty;
  var golden_epcm_2004 : epcm_entry_ty;

  var allow_adversary : bool;


  //get desired values of secs, tcs, pages
  call init();
  attributes := Attributes(false);
  secs := Secs(2000, 5, false, 0, hash(signing_key), 0, 0, attributes);
  call ecreate(2000, secs);      
  tcs := Tcs(false, false, 3, 2, 0); 
  call eadd_tcs(2001, 2000, tcs);
  call eadd_reg(2002, 2000, secret1);
  call eadd_reg(2003, 2000, abort_data);
  call eadd_reg(2004, 2000, abort_data);
  call eextend(2001); 
  call eextend(2002); 
  call eextend(2003); 
  call eextend(2004); 
  assume desired_measurement == Secs_mrenclave(mem_secs[page_table[2000]]); //HACK, but I see no other way
  sigstruct := Sigstruct(signing_key, desired_measurement, attributes, 0, 0);
  signature := encrypt(signing_key, hash(sigstruct));
  sigstruct_signed := Sigstruct_signed(signature, sigstruct);
  einittoken := Einittoken(true, attributes, desired_measurement, hash(signing_key));
  call einit(sigstruct_signed, 2000, einittoken);
  call eenter(2001);
 
  golden_secs := mem_secs[page_table[2000]];
  golden_tcs := mem_tcs[page_table[2001]];
  golden_reg := mem_reg[page_table[2002]];
  golden_lpstate := lp_state[curr_lp];
  golden_epcm_2000 := epcm[page_table[2000]];
  golden_epcm_2001 := epcm[page_table[2001]];
  golden_epcm_2002 := epcm[page_table[2002]];
  golden_epcm_2003 := epcm[page_table[2003]];
  golden_epcm_2004 := epcm[page_table[2004]];

  //bring system to arbitrary state s1
  havoc epcm; havoc lp_state; havoc xstate;
  havoc mem_reg; havoc mem_secs; havoc mem_tcs;

  //cache current state into s1
  epcm1 := epcm; lp_state1 := lp_state; xstate1 := xstate; page_table1 := page_table;
  mem_reg1 := mem_reg; mem_secs1 := mem_secs; mem_tcs1 := mem_tcs;
  
  call interrupt();

  //cache current state into s1_next
  next_epcm1 := epcm; next_lp_state1 := lp_state; next_xstate1 := xstate; next_page_table1 := page_table;
  next_mem_reg1 := mem_reg; next_mem_secs1 := mem_secs; next_mem_tcs1 := mem_tcs;
 
  call adversary_func();

  //cache current state into s1_next_next
  next_next_epcm1 := epcm; next_next_lp_state1 := lp_state; next_next_xstate1 := xstate; next_next_page_table1 := page_table;
  next_next_mem_reg1 := mem_reg; next_next_mem_secs1 := mem_secs; next_next_mem_tcs1 := mem_tcs;

  assume page_table[interrupted_thread] == Lp_state_cr_tcs_pa(lp_state1[curr_lp]);
  call eresume_with_assumptions(interrupted_thread);

  //cache current state into s1_next_next_next
  next_next_next_epcm1 := epcm; next_next_next_lp_state1 := lp_state; next_next_next_xstate1 := xstate; next_next_next_page_table1 := page_table;
  next_next_next_mem_reg1 := mem_reg; next_next_next_mem_secs1 := mem_secs; next_next_next_mem_tcs1 := mem_tcs;



  //bring system to arbitrary state s2
  havoc epcm; havoc lp_state; havoc xstate;
  havoc mem_reg; havoc mem_secs; havoc mem_tcs;

  //cache current state into s2
  epcm2 := epcm; lp_state2 := lp_state; xstate2 := xstate; page_table2 := page_table;
  mem_reg2 := mem_reg; mem_secs2 := mem_secs; mem_tcs2 := mem_tcs;
  
  call interrupt();

  //cache current state into s2_next
  next_epcm2 := epcm; next_lp_state2 := lp_state; next_xstate2 := xstate; next_page_table2 := page_table;
  next_mem_reg2 := mem_reg; next_mem_secs2 := mem_secs; next_mem_tcs2 := mem_tcs;
 
  call skip();

  //cache current state into s2_next_next
  next_next_epcm2 := epcm; next_next_lp_state2 := lp_state; next_next_xstate2 := xstate; next_next_page_table2 := page_table;
  next_next_mem_reg2 := mem_reg; next_next_mem_secs2 := mem_secs; next_next_mem_tcs2 := mem_tcs;

  assume page_table[interrupted_thread] == Lp_state_cr_tcs_pa(lp_state1[curr_lp]);
  call eresume_with_assumptions(interrupted_thread);

  //cache current state into s2_next_next_next
  next_next_next_epcm2 := epcm; next_next_next_lp_state2 := lp_state; next_next_next_xstate2 := xstate; next_next_next_page_table2 := page_table;
  next_next_next_mem_reg2 := mem_reg; next_next_next_mem_secs2 := mem_secs; next_next_next_mem_tcs2 := mem_tcs;


  aux := epcm1[2000] == epcm2[2000] && 
         epcm1[2001] == epcm2[2001] && 
         epcm1[2002] == epcm2[2002] && 
         epcm1[2003] == epcm2[2003] && 
         epcm1[2004] == epcm2[2004] && 
         mem_secs1[2000] == mem_secs2[2000] && 
         mem_tcs1[2001] == mem_tcs2[2001] && 
         mem_reg1[2002] == mem_reg2[2002] && 
         lp_state1[curr_lp] == lp_state2[curr_lp] &&
         (forall i: physical_address :: (i < 2000 || i > 2004) ==> 
                                        (Epcm_enclavesecs(epcm1[i]) < 2000 || 
                                         Epcm_enclavesecs(epcm1[i]) > 2004));

  aux_const := mem_secs1[2000] == golden_secs &&
               Tcs_ossa(mem_tcs1[2001]) == Tcs_ossa(golden_tcs) &&
               Tcs_nssa(mem_tcs1[2001]) == Tcs_nssa(golden_tcs) &&
               epcm1[2000] == golden_epcm_2000 &&
               epcm1[2001] == golden_epcm_2001 &&
               epcm1[2002] == golden_epcm_2002 &&
               epcm1[2003] == golden_epcm_2003 &&
               epcm1[2004] == golden_epcm_2004 &&
               lp_state1[curr_lp] == golden_lpstate;


  aux_next := next_epcm1[2000] == next_epcm2[2000] && 
         next_epcm1[2001] == next_epcm2[2001] && 
         next_epcm1[2002] == next_epcm2[2002] && 
         next_epcm1[2003] == next_epcm2[2003] && 
         next_epcm1[2004] == next_epcm2[2004] && 
         next_mem_secs1[2000] == next_mem_secs2[2000] && 
         next_mem_tcs1[2001] == next_mem_tcs2[2001] && 
         next_mem_reg1[2002] == next_mem_reg2[2002] && 
         //next_lp_state1[curr_lp] == next_lp_state2[curr_lp] &&
         (forall i: physical_address :: (i < 2000 || i > 2004) ==> 
                                        (Epcm_enclavesecs(next_epcm1[i]) < 2000 || 
                                         Epcm_enclavesecs(next_epcm1[i]) > 2004));

  aux_next_const := next_mem_secs1[2000] == golden_secs &&
               Tcs_ossa(next_mem_tcs1[2001]) == Tcs_ossa(golden_tcs) &&
               Tcs_nssa(next_mem_tcs1[2001]) == Tcs_nssa(golden_tcs) &&
               next_epcm1[2000] == golden_epcm_2000 &&
               next_epcm1[2001] == golden_epcm_2001 &&
               next_epcm1[2002] == golden_epcm_2002 &&
               next_epcm1[2003] == golden_epcm_2003 &&
               next_epcm1[2004] == golden_epcm_2004; 

  aux_next_next := next_next_epcm1[2000] == next_next_epcm2[2000] && 
         next_next_epcm1[2001] == next_next_epcm2[2001] && 
         next_next_epcm1[2002] == next_next_epcm2[2002] && 
         next_next_epcm1[2003] == next_next_epcm2[2003] && 
         next_next_epcm1[2004] == next_next_epcm2[2004] && 
         next_next_mem_secs1[2000] == next_next_mem_secs2[2000] && 
         next_next_mem_tcs1[2001] == next_next_mem_tcs2[2001] && 
         next_next_mem_reg1[2002] == next_next_mem_reg2[2002] && 
         //next_next_lp_state1[curr_lp] == next_next_lp_state2[curr_lp] &&
         (forall i: physical_address :: (i < 2000 || i > 2004) ==> 
                                        (Epcm_enclavesecs(next_next_epcm1[i]) < 2000 || 
                                         Epcm_enclavesecs(next_next_epcm1[i]) > 2004));

  aux_next_next_const := next_next_mem_secs1[2000] == golden_secs &&
               Tcs_ossa(next_next_mem_tcs1[2001]) == Tcs_ossa(golden_tcs) &&
               Tcs_nssa(next_next_mem_tcs1[2001]) == Tcs_nssa(golden_tcs) &&
               next_next_epcm1[2000] == golden_epcm_2000 &&
               next_next_epcm1[2001] == golden_epcm_2001 &&
               next_next_epcm1[2002] == golden_epcm_2002 &&
               next_next_epcm1[2003] == golden_epcm_2003 &&
               next_next_epcm1[2004] == golden_epcm_2004; 

  aux_next_next_next := next_next_next_epcm1[2000] == next_next_next_epcm2[2000] && 
         next_next_next_epcm1[2001] == next_next_next_epcm2[2001] && 
         next_next_next_epcm1[2002] == next_next_next_epcm2[2002] && 
         next_next_next_epcm1[2003] == next_next_next_epcm2[2003] && 
         next_next_next_epcm1[2004] == next_next_next_epcm2[2004] && 
         next_next_next_mem_secs1[2000] == next_next_next_mem_secs2[2000] && 
         next_next_next_mem_tcs1[2001] == next_next_next_mem_tcs2[2001] && 
         next_next_next_mem_reg1[2002] == next_next_next_mem_reg2[2002] && 
         //next_next_next_lp_state1[curr_lp] == next_next_next_lp_state2[curr_lp] &&
         (forall i: physical_address :: (i < 2000 || i > 2004) ==> 
                                        (Epcm_enclavesecs(next_next_next_epcm1[i]) < 2000 || 
                                         Epcm_enclavesecs(next_next_next_epcm1[i]) > 2004));

  aux_next_next_next_const := next_next_next_mem_secs1[2000] == golden_secs &&
               Tcs_ossa(next_next_next_mem_tcs1[2001]) == Tcs_ossa(golden_tcs) &&
               Tcs_nssa(next_next_next_mem_tcs1[2001]) == Tcs_nssa(golden_tcs) &&
               next_next_next_epcm1[2000] == golden_epcm_2000 &&
               next_next_next_epcm1[2001] == golden_epcm_2001 &&
               next_next_next_epcm1[2002] == golden_epcm_2002 &&
               next_next_next_epcm1[2003] == golden_epcm_2003 &&
               next_next_next_epcm1[2004] == golden_epcm_2004; 

  assert (aux && aux_const) ==> (aux_next && aux_next_const); 
  assert (aux_next && aux_next_const) ==> (aux_next_next && aux_next_next_const); 
  assert (aux_next_next && aux_next_next_const) ==> (aux_next_next_next && aux_next_next_next_const); 
}


procedure adversary_havoc_reduction_proof()
modifies mem_reg, mem_tcs, mem_secs, epcm, lp_state, xstate, page_table, curr_lp, arbitrary_write_count;
{
  var phi: bool; var phi_next: bool;
  var aux: bool; var aux_next: bool;
  var aux_const: bool; var aux_next_const: bool;

  //variable declarations
  var mem_reg1: [physical_address] data; var mem_reg2: [physical_address] data;
  var mem_secs1: [physical_address] secs_ty; var mem_secs2: [physical_address] secs_ty;
  var mem_tcs1: [physical_address] tcs_ty; var mem_tcs2: [physical_address] tcs_ty;
  var epcm1 : [physical_address] epcm_entry_ty; var epcm2 : [physical_address] epcm_entry_ty;
  var lp_state1 : [lp_id] lp_state_ty; var lp_state2 : [lp_id] lp_state_ty;
  var xstate1 : [lp_id] xstate_ty; var xstate2 : [lp_id] xstate_ty;
  var page_table1 : page_table_ty; var page_table2 : page_table_ty;
  var next_mem_reg1: [physical_address] data; var next_mem_reg2: [physical_address] data;
  var next_mem_secs1: [physical_address] secs_ty; var next_mem_secs2: [physical_address] secs_ty;
  var next_mem_tcs1: [physical_address] tcs_ty; var next_mem_tcs2: [physical_address] tcs_ty;
  var next_epcm1 : [physical_address] epcm_entry_ty; var next_epcm2 : [physical_address] epcm_entry_ty;
  var next_lp_state1 : [lp_id] lp_state_ty; var next_lp_state2 : [lp_id] lp_state_ty;
  var next_xstate1 : [lp_id] xstate_ty; var next_xstate2 : [lp_id] xstate_ty;
  var next_page_table1 : page_table_ty; var next_page_table2 : page_table_ty;

  var targetinfo: targetinfo_ty; var targetinfo_next: targetinfo_ty;
  var reportdata: data; var reportdata_next: data;
  var s1_ereport_result : report_maced_ty; var s2_ereport_result : report_maced_ty;
  var s1_next_ereport_result : report_maced_ty; var s2_next_ereport_result : report_maced_ty;
  var s1_egetkey_result : key_ty; var s2_egetkey_result : key_ty;
  var s1_next_egetkey_result : key_ty; var s2_next_egetkey_result : key_ty;
  var s1_read_result: data; var s2_read_result: data;
  var s1_next_read_result: data; var s2_next_read_result: data;

  var tmp_ereport_result: report_maced_ty;
  var tmp_egetkey_result: key_ty;
  var tmp_read_result: data;

  var secs : secs_ty;
  var tcs : tcs_ty;
  var signing_key : key_ty;
  var desired_measurement : measurement_ty;
  var secret1: data;
  var attributes: attributes_ty;
  var signature : ciphertext_ty (hashtext_ty sigstruct_ty);
  var sigstruct: sigstruct_ty;
  var sigstruct_signed: sigstruct_signed_ty;
  var einittoken: einittoken_ty;

  var golden_secs : secs_ty;
  var golden_tcs : tcs_ty;
  var golden_reg : data;
  var golden_lpstate : lp_state_ty;
  var golden_epcm_2000 : epcm_entry_ty;
  var golden_epcm_2001 : epcm_entry_ty;
  var golden_epcm_2002 : epcm_entry_ty;
  var golden_epcm_2003 : epcm_entry_ty;
  var golden_epcm_2004 : epcm_entry_ty;

  var cachemem1 : [physical_address] data;
  var cachetable1: page_table_ty;
  var cachemem2 : [physical_address] data;
  var cachetable2: page_table_ty;
  var thetamem : [physical_address] data;
  var thetatable: page_table_ty;


  //get desired values of secs, tcs, pages
  call init();
  attributes := Attributes(false);
  secs := Secs(2000, 5, false, 0, hash(signing_key), 0, 0, attributes);
  call ecreate(2000, secs);      
  tcs := Tcs(false, false, 3, 2, 0); 
  call eadd_tcs(2001, 2000, tcs);
  call eadd_reg(2002, 2000, secret1);
  call eadd_reg(2003, 2000, abort_data);
  call eadd_reg(2004, 2000, abort_data);
  call eextend(2001); 
  call eextend(2002); 
  call eextend(2003); 
  call eextend(2004); 
  assume desired_measurement == Secs_mrenclave(mem_secs[page_table[2000]]); //HACK, but I see no other way
  sigstruct := Sigstruct(signing_key, desired_measurement, attributes, 0, 0);
  signature := encrypt(signing_key, hash(sigstruct));
  sigstruct_signed := Sigstruct_signed(signature, sigstruct);
  einittoken := Einittoken(true, attributes, desired_measurement, hash(signing_key));
  call einit(sigstruct_signed, 2000, einittoken);
  call eenter(2001);
 
  golden_secs := mem_secs[page_table[2000]];
  golden_tcs := mem_tcs[page_table[2001]];
  golden_reg := mem_reg[page_table[2002]];
  golden_lpstate := lp_state[curr_lp];
  golden_epcm_2000 := epcm[page_table[2000]];
  golden_epcm_2001 := epcm[page_table[2001]];
  golden_epcm_2002 := epcm[page_table[2002]];
  golden_epcm_2003 := epcm[page_table[2003]];
  golden_epcm_2004 := epcm[page_table[2004]];

  //bring system to arbitrary state s1
  //FIXME: what happened to the page table havoc?
  havoc epcm; havoc lp_state; havoc xstate;
  havoc mem_reg; havoc mem_secs; havoc mem_tcs;
  
  //cache current state into s1
  epcm1 := epcm; lp_state1 := lp_state; xstate1 := xstate; page_table1 := page_table;
  mem_reg1 := mem_reg; mem_secs1 := mem_secs; mem_tcs1 := mem_tcs;

  //make API call from s1, side-effect on system takes it to s1'
  call s1_ereport_result, s1_egetkey_result, s1_read_result := enclave_operation(1);
  


  //bring system to arbitrary state s2
  havoc epcm; havoc lp_state; havoc xstate; 
  havoc mem_reg; havoc mem_secs; havoc mem_tcs;

  //cache current state into s2
  epcm2 := epcm; lp_state2 := lp_state; xstate2 := xstate; page_table2 := page_table;
  mem_reg2 := mem_reg; mem_secs2 := mem_secs; mem_tcs2 := mem_tcs;

  //make API call from s2, side-effect on system takes it to s2'
  call s2_ereport_result, s2_egetkey_result, s2_read_result := enclave_operation(1);
  /* FIXED on Nov 9, 2014
  aux := epcm1[page_table1[2000]] == epcm2[page_table2[2000]] && 
         epcm1[page_table1[2001]] == epcm2[page_table2[2001]] && 
         epcm1[page_table1[2002]] == epcm2[page_table2[2002]] && 
         epcm1[page_table1[2003]] == epcm2[page_table2[2003]] && 
         epcm1[page_table1[2004]] == epcm2[page_table2[2004]] && 
         mem_secs1[page_table1[2000]] == mem_secs2[page_table2[2000]] && 
         mem_tcs1[page_table1[2001]] == mem_tcs2[page_table2[2001]] && 
         mem_reg1[page_table1[2002]] == mem_reg2[page_table2[2002]] &&
         lp_state1[curr_lp] == lp_state2[curr_lp] &&
         (forall i: physical_address :: (i < 2000 || i > 2004) ==> 
                                        (Epcm_enclavesecs(epcm1[i]) < 2000 || 
                                         Epcm_enclavesecs(epcm1[i]) > 2004));
  aux_const := mem_secs1[page_table1[2000]] == golden_secs &&
               mem_tcs1[page_table1[2001]] == golden_tcs &&
               epcm1[page_table1[2000]] == golden_epcm_2000 &&
               epcm1[page_table1[2001]] == golden_epcm_2001 &&
               epcm1[page_table1[2002]] == golden_epcm_2002 &&
               epcm1[page_table1[2003]] == golden_epcm_2003 &&
               epcm1[page_table1[2004]] == golden_epcm_2004 &&
               lp_state[curr_lp] == golden_lpstate;
  */
  aux := epcm1[2000] == epcm2[2000] && 
         epcm1[2001] == epcm2[2001] && 
         epcm1[2002] == epcm2[2002] && 
         epcm1[2003] == epcm2[2003] && 
         epcm1[2004] == epcm2[2004] && 
         mem_secs1[2000] == mem_secs2[2000] && 
         mem_tcs1[2001] == mem_tcs2[2001] && 
         mem_reg1[2002] == mem_reg2[2002] && 
         lp_state1[curr_lp] == lp_state2[curr_lp] &&
         (forall i: physical_address :: (i < 2000 || i > 2004) ==> 
                                        (Epcm_enclavesecs(epcm1[i]) < 2000 || 
                                         Epcm_enclavesecs(epcm1[i]) > 2004));

  aux_const := mem_secs1[2000] == golden_secs &&
               mem_tcs1[2001] == golden_tcs &&
               epcm1[2000] == golden_epcm_2000 &&
               epcm1[2001] == golden_epcm_2001 &&
               epcm1[2002] == golden_epcm_2002 &&
               epcm1[2003] == golden_epcm_2003 &&
               epcm1[2004] == golden_epcm_2004 &&
               lp_state1[curr_lp] == golden_lpstate;

  phi := ((enclave_operation_choose(1) == EREPORT) ==> (s1_ereport_result == s2_ereport_result)) &&
         ((enclave_operation_choose(1) == EGETKEY) ==> (s1_egetkey_result == s2_egetkey_result)) &&
         ((enclave_operation_choose(1) == READ) ==> (s1_read_result == s2_read_result));

  assume aux && aux_const && phi;


  //take 1 step transition from s1 to s1_next by allowing the adversary to do things
  epcm := epcm1; lp_state := lp_state1; xstate := xstate1; page_table := page_table1;
  mem_reg := mem_reg1; mem_secs := mem_secs1; mem_tcs := mem_tcs1;

  //ADVERSARY
  call osvmm_adversary();
  cachemem1 := mem_reg;
  cachetable1 := page_table;
  havoc mem_reg;
  havoc page_table;
  assume (forall a: physical_address :: (is_epc_address(a)) ==> (mem_reg[a] == cachemem1[a])); //can't havoc EPC memory
  thetamem := mem_reg;
  thetatable := page_table;

  //cache current state into s1_next
  next_epcm1 := epcm; next_lp_state1 := lp_state; next_xstate1 := xstate; next_page_table1 := page_table;
  next_mem_reg1 := mem_reg; next_mem_secs1 := mem_secs; next_mem_tcs1 := mem_tcs;

  //make API call from s1_next, side-effect on system takes it to s1_next'
  call s1_next_ereport_result, s1_next_egetkey_result, s1_next_read_result := enclave_operation(2);



  //take 1 step transition from s2 to s2_next by allowing the adversary to do things
  epcm := epcm2; lp_state := lp_state2; xstate := xstate2; page_table := page_table2;
  mem_reg := mem_reg2; mem_secs := mem_secs2; mem_tcs := mem_tcs2;

  //OTHER ADVERSARY
  cachemem2 := mem_reg;
  cachetable2 := page_table;
  havoc mem_reg;
  assume (forall a: physical_address :: (is_epc_address(a)) ==> (mem_reg[a] == cachemem2[a])); //can't havoc EPC memory
  assume (forall a: linear_address :: (!in_register_range(a, Lp_state_cr_elrange(lp_state[curr_lp]))) ==> (mem_reg[page_table[a]] == thetamem[thetatable[a]]));

  //cache current state into s2_next
  next_epcm2 := epcm; next_lp_state2 := lp_state; next_xstate2 := xstate; next_page_table2 := page_table;
  next_mem_reg2 := mem_reg; next_mem_secs2 := mem_secs; next_mem_tcs2 := mem_tcs;

  //make API call from s2_next, side-effect on system takes it to s2_next'
  call s2_next_ereport_result, s2_next_egetkey_result, s2_next_read_result := enclave_operation(2);

  phi_next := ((enclave_operation_choose(2) == EREPORT) ==> (s1_next_ereport_result == s2_next_ereport_result)) &&
              ((enclave_operation_choose(2) == EGETKEY) ==> (s1_next_egetkey_result == s2_next_egetkey_result)) &&
              ((enclave_operation_choose(2) == READ) ==> (s1_next_read_result == s2_next_read_result));
  /*
  aux_next := next_epcm1[next_page_table1[2000]] == next_epcm2[next_page_table2[2000]] && 
         next_epcm1[next_page_table1[2001]] == next_epcm2[next_page_table2[2001]] && 
         next_epcm1[next_page_table1[2002]] == next_epcm2[next_page_table2[2002]] && 
         next_epcm1[next_page_table1[2003]] == next_epcm2[next_page_table2[2003]] && 
         next_epcm1[next_page_table1[2004]] == next_epcm2[next_page_table2[2004]] && 
         next_mem_secs1[next_page_table1[2000]] == next_mem_secs2[next_page_table2[2000]] && 
         next_mem_tcs1[next_page_table1[2001]] == next_mem_tcs2[next_page_table2[2001]] && 
         next_mem_reg1[next_page_table1[2002]] == next_mem_reg2[next_page_table2[2002]] && 
         next_lp_state1[curr_lp] == next_lp_state2[curr_lp] &&
         (forall i: physical_address :: (i < 2000 || i > 2004) ==> 
                                        (Epcm_enclavesecs(next_epcm1[i]) < 2000 || 
                                         Epcm_enclavesecs(next_epcm1[i]) > 2004));
  aux_next_const := next_mem_secs1[next_page_table1[2000]] == golden_secs &&
               next_mem_tcs1[next_page_table1[2001]] == golden_tcs &&
               next_epcm1[next_page_table1[2000]] == golden_epcm_2000 &&
               next_epcm1[next_page_table1[2001]] == golden_epcm_2001 &&
               next_epcm1[next_page_table1[2002]] == golden_epcm_2002 &&
               next_epcm1[next_page_table1[2003]] == golden_epcm_2003 &&
               next_epcm1[next_page_table1[2004]] == golden_epcm_2004 &&
               next_lp_state1[curr_lp] == golden_lpstate;
  */
  aux_next := next_epcm1[2000] == next_epcm2[2000] && 
         next_epcm1[2001] == next_epcm2[2001] && 
         next_epcm1[2002] == next_epcm2[2002] && 
         next_epcm1[2003] == next_epcm2[2003] && 
         next_epcm1[2004] == next_epcm2[2004] && 
         next_mem_secs1[2000] == next_mem_secs2[2000] && 
         next_mem_tcs1[2001] == next_mem_tcs2[2001] && 
         next_mem_reg1[2002] == next_mem_reg2[2002] && 
         next_lp_state1[curr_lp] == next_lp_state2[curr_lp] &&
         (forall i: physical_address :: (i < 2000 || i > 2004) ==> 
                                        (Epcm_enclavesecs(next_epcm1[i]) < 2000 || 
                                         Epcm_enclavesecs(next_epcm1[i]) > 2004));

  aux_next_const := next_mem_secs1[2000] == golden_secs &&
               next_mem_tcs1[2001] == golden_tcs &&
               next_epcm1[2000] == golden_epcm_2000 &&
               next_epcm1[2001] == golden_epcm_2001 &&
               next_epcm1[2002] == golden_epcm_2002 &&
               next_epcm1[2003] == golden_epcm_2003 &&
               next_epcm1[2004] == golden_epcm_2004 &&
               next_lp_state1[curr_lp] == golden_lpstate;

  assert (phi_next && aux_next && aux_next_const);
}

/* Proof for the integrity component of non-interference */
procedure integrity_proof()
modifies mem_reg, mem_tcs, mem_secs, epcm, lp_state, xstate, page_table, curr_lp, arbitrary_write_count;
{
  var phi: bool; var phi_next: bool;
  var aux: bool; var aux_next: bool;
  var aux_const: bool; var aux_next_const: bool;

  //variable declarations
  var mem_reg1: [physical_address] data; var mem_reg2: [physical_address] data;
  var mem_secs1: [physical_address] secs_ty; var mem_secs2: [physical_address] secs_ty;
  var mem_tcs1: [physical_address] tcs_ty; var mem_tcs2: [physical_address] tcs_ty;
  var epcm1 : [physical_address] epcm_entry_ty; var epcm2 : [physical_address] epcm_entry_ty;
  var lp_state1 : [lp_id] lp_state_ty; var lp_state2 : [lp_id] lp_state_ty;
  var xstate1 : [lp_id] xstate_ty; var xstate2 : [lp_id] xstate_ty;
  var page_table1 : page_table_ty; var page_table2 : page_table_ty;
  var next_mem_reg1: [physical_address] data; var next_mem_reg2: [physical_address] data;
  var next_mem_secs1: [physical_address] secs_ty; var next_mem_secs2: [physical_address] secs_ty;
  var next_mem_tcs1: [physical_address] tcs_ty; var next_mem_tcs2: [physical_address] tcs_ty;
  var next_epcm1 : [physical_address] epcm_entry_ty; var next_epcm2 : [physical_address] epcm_entry_ty;
  var next_lp_state1 : [lp_id] lp_state_ty; var next_lp_state2 : [lp_id] lp_state_ty;
  var next_xstate1 : [lp_id] xstate_ty; var next_xstate2 : [lp_id] xstate_ty;
  var next_page_table1 : page_table_ty; var next_page_table2 : page_table_ty;

  var targetinfo: targetinfo_ty; var targetinfo_next: targetinfo_ty;
  var reportdata: data; var reportdata_next: data;
  var s1_ereport_result : report_maced_ty; var s2_ereport_result : report_maced_ty;
  var s1_next_ereport_result : report_maced_ty; var s2_next_ereport_result : report_maced_ty;
  var s1_egetkey_result : key_ty; var s2_egetkey_result : key_ty;
  var s1_next_egetkey_result : key_ty; var s2_next_egetkey_result : key_ty;
  var s1_read_result: data; var s2_read_result: data;
  var s1_next_read_result: data; var s2_next_read_result: data;

  var tmp_ereport_result: report_maced_ty;
  var tmp_egetkey_result: key_ty;
  var tmp_read_result: data;

  var secs : secs_ty;
  var tcs : tcs_ty;
  var signing_key : key_ty;
  var desired_measurement : measurement_ty;
  var secret1: data;
  var attributes: attributes_ty;
  var signature : ciphertext_ty (hashtext_ty sigstruct_ty);
  var sigstruct: sigstruct_ty;
  var sigstruct_signed: sigstruct_signed_ty;
  var einittoken: einittoken_ty;

  var golden_secs : secs_ty;
  var golden_tcs : tcs_ty;
  var golden_reg : data;
  var golden_lpstate : lp_state_ty;
  var golden_epcm_2000 : epcm_entry_ty;
  var golden_epcm_2001 : epcm_entry_ty;
  var golden_epcm_2002 : epcm_entry_ty;
  var golden_epcm_2003 : epcm_entry_ty;
  var golden_epcm_2004 : epcm_entry_ty;

  var allow_adversary : bool;


  //get desired values of secs, tcs, pages
  call init();
  attributes := Attributes(false);
  secs := Secs(2000, 5, false, 0, hash(signing_key), 0, 0, attributes);
  call ecreate(2000, secs);      
  tcs := Tcs(false, false, 3, 2, 0); 
  call eadd_tcs(2001, 2000, tcs);
  call eadd_reg(2002, 2000, secret1);
  call eadd_reg(2003, 2000, abort_data);
  call eadd_reg(2004, 2000, abort_data);
  call eextend(2001); 
  call eextend(2002); 
  call eextend(2003); 
  call eextend(2004); 
  assume desired_measurement == Secs_mrenclave(mem_secs[page_table[2000]]); //HACK, but I see no other way
  sigstruct := Sigstruct(signing_key, desired_measurement, attributes, 0, 0);
  signature := encrypt(signing_key, hash(sigstruct));
  sigstruct_signed := Sigstruct_signed(signature, sigstruct);
  einittoken := Einittoken(true, attributes, desired_measurement, hash(signing_key));
  call einit(sigstruct_signed, 2000, einittoken);
  call eenter(2001);
 
  golden_secs := mem_secs[page_table[2000]];
  golden_tcs := mem_tcs[page_table[2001]];
  golden_reg := mem_reg[page_table[2002]];
  golden_lpstate := lp_state[curr_lp];
  golden_epcm_2000 := epcm[page_table[2000]];
  golden_epcm_2001 := epcm[page_table[2001]];
  golden_epcm_2002 := epcm[page_table[2002]];
  golden_epcm_2003 := epcm[page_table[2003]];
  golden_epcm_2004 := epcm[page_table[2004]];

  //bring system to arbitrary state s1
  havoc epcm; havoc lp_state; havoc xstate;
  havoc mem_reg; havoc mem_secs; havoc mem_tcs;
  
  //cache current state into s1
  epcm1 := epcm; lp_state1 := lp_state; xstate1 := xstate; page_table1 := page_table;
  mem_reg1 := mem_reg; mem_secs1 := mem_secs; mem_tcs1 := mem_tcs;

  //make API call from s1, side-effect on system takes it to s1'
  call s1_ereport_result, s1_egetkey_result, s1_read_result := enclave_operation(1);
  


  //bring system to arbitrary state s2
  havoc epcm; havoc lp_state; havoc xstate; 
  havoc mem_reg; havoc mem_secs; havoc mem_tcs;

  //cache current state into s2
  epcm2 := epcm; lp_state2 := lp_state; xstate2 := xstate; page_table2 := page_table;
  mem_reg2 := mem_reg; mem_secs2 := mem_secs; mem_tcs2 := mem_tcs;

  //make API call from s2, side-effect on system takes it to s2'
  call s2_ereport_result, s2_egetkey_result, s2_read_result := enclave_operation(1);

  /*
  aux := epcm1[page_table1[2000]] == epcm2[page_table2[2000]] && 
         epcm1[page_table1[2001]] == epcm2[page_table2[2001]] && 
         epcm1[page_table1[2002]] == epcm2[page_table2[2002]] && 
         epcm1[page_table1[2003]] == epcm2[page_table2[2003]] && 
         epcm1[page_table1[2004]] == epcm2[page_table2[2004]] && 
         mem_secs1[page_table1[2000]] == mem_secs2[page_table2[2000]] && 
         mem_tcs1[page_table1[2001]] == mem_tcs2[page_table2[2001]] && 
         mem_reg1[page_table1[2002]] == mem_reg2[page_table2[2002]] &&
         lp_state1[curr_lp] == lp_state2[curr_lp] &&
         (forall i: physical_address :: (i < 2000 || i > 2004) ==> 
                                        (Epcm_enclavesecs(epcm1[i]) < 2000 || 
                                         Epcm_enclavesecs(epcm1[i]) > 2004));
  aux_const := mem_secs1[page_table1[2000]] == golden_secs &&
               mem_tcs1[page_table1[2001]] == golden_tcs &&
               epcm1[page_table1[2000]] == golden_epcm_2000 &&
               epcm1[page_table1[2001]] == golden_epcm_2001 &&
               epcm1[page_table1[2002]] == golden_epcm_2002 &&
               epcm1[page_table1[2003]] == golden_epcm_2003 &&
               epcm1[page_table1[2004]] == golden_epcm_2004 &&
               lp_state[curr_lp] == golden_lpstate;
  */
  aux := epcm1[page_table1[2000]] == epcm2[page_table2[2000]] && 
         epcm1[page_table1[2001]] == epcm2[page_table2[2001]] && 
         epcm1[page_table1[2002]] == epcm2[page_table2[2002]] && 
         epcm1[page_table1[2003]] == epcm2[page_table2[2003]] && 
         epcm1[page_table1[2004]] == epcm2[page_table2[2004]] && 
         mem_secs1[page_table1[2000]] == mem_secs2[page_table2[2000]] && 
         mem_tcs1[page_table1[2001]] == mem_tcs2[page_table2[2001]] && 
         mem_reg1[page_table1[2002]] == mem_reg2[page_table2[2002]] &&
         lp_state1[curr_lp] == lp_state2[curr_lp] &&
         (forall i: physical_address :: (i < 2000 || i > 2004) ==> 
                                        (Epcm_enclavesecs(epcm1[i]) < 2000 || 
                                         Epcm_enclavesecs(epcm1[i]) > 2004));
  aux_const := mem_secs1[page_table1[2000]] == golden_secs &&
               mem_tcs1[page_table1[2001]] == golden_tcs &&
               epcm1[page_table1[2000]] == golden_epcm_2000 &&
               epcm1[page_table1[2001]] == golden_epcm_2001 &&
               epcm1[page_table1[2002]] == golden_epcm_2002 &&
               epcm1[page_table1[2003]] == golden_epcm_2003 &&
               epcm1[page_table1[2004]] == golden_epcm_2004 &&
               lp_state[curr_lp] == golden_lpstate;


  phi := ((enclave_operation_choose(1) == EREPORT) ==> (s1_ereport_result == s2_ereport_result)) &&
         ((enclave_operation_choose(1) == EGETKEY) ==> (s1_egetkey_result == s2_egetkey_result)) &&
         ((enclave_operation_choose(1) == READ) ==> (s1_read_result == s2_read_result));
  assume aux && aux_const && phi;


  //take 1 step transition from s1 to s1_next by allowing the adversary to do things
  epcm := epcm1; lp_state := lp_state1; xstate := xstate1; page_table := page_table1;
  mem_reg := mem_reg1; mem_secs := mem_secs1; mem_tcs := mem_tcs1;

  if (allow_adversary) {
    call osvmm_adversary();
  } else {
    call tmp_ereport_result, tmp_egetkey_result, tmp_read_result := enclave_operation(0);
  }

  //cache current state into s1_next
  next_epcm1 := epcm; next_lp_state1 := lp_state; next_xstate1 := xstate; next_page_table1 := page_table;
  next_mem_reg1 := mem_reg; next_mem_secs1 := mem_secs; next_mem_tcs1 := mem_tcs;

  //make API call from s1_next, side-effect on system takes it to s1_next'
  call s1_next_ereport_result, s1_next_egetkey_result, s1_next_read_result := enclave_operation(2);



  //take 1 step transition from s2 to s2_next by allowing the adversary to do things
  epcm := epcm2; lp_state := lp_state2; xstate := xstate2; page_table := page_table2;
  mem_reg := mem_reg2; mem_secs := mem_secs2; mem_tcs := mem_tcs2;

  if(allow_adversary) {
    call skip();
  } else {
    call tmp_ereport_result, tmp_egetkey_result, tmp_read_result := enclave_operation(0);
  }

  //cache current state into s2_next
  next_epcm2 := epcm; next_lp_state2 := lp_state; next_xstate2 := xstate; next_page_table2 := page_table;
  next_mem_reg2 := mem_reg; next_mem_secs2 := mem_secs; next_mem_tcs2 := mem_tcs;

  //make API call from s2_next, side-effect on system takes it to s2_next'
  call s2_next_ereport_result, s2_next_egetkey_result, s2_next_read_result := enclave_operation(2);

  phi_next := ((enclave_operation_choose(2) == EREPORT) ==> (s1_next_ereport_result == s2_next_ereport_result)) &&
              ((enclave_operation_choose(2) == EGETKEY) ==> (s1_next_egetkey_result == s2_next_egetkey_result)) &&
              ((enclave_operation_choose(2) == READ) ==> (s1_next_read_result == s2_next_read_result));
  /*
  aux_next := next_epcm1[page_table1[2000]] == next_epcm2[page_table2[2000]] && 
         next_epcm1[page_table1[2001]] == next_epcm2[page_table2[2001]] && 
         next_epcm1[page_table1[2002]] == next_epcm2[page_table2[2002]] && 
         next_epcm1[page_table1[2003]] == next_epcm2[page_table2[2003]] && 
         next_epcm1[page_table1[2004]] == next_epcm2[page_table2[2004]] && 
         next_mem_secs1[page_table1[2000]] == next_mem_secs2[page_table2[2000]] && 
         next_mem_tcs1[page_table1[2001]] == next_mem_tcs2[page_table2[2001]] && 
         next_mem_reg1[page_table1[2002]] == next_mem_reg2[page_table2[2002]] && 
         next_lp_state1[curr_lp] == next_lp_state2[curr_lp] &&
         (forall i: physical_address :: (i < 2000 || i > 2004) ==> 
                                        (Epcm_enclavesecs(next_epcm1[i]) < 2000 || 
                                         Epcm_enclavesecs(next_epcm1[i]) > 2004));
  aux_next_const := next_mem_secs1[page_table[2000]] == golden_secs &&
               next_mem_tcs1[page_table[2001]] == golden_tcs &&
               next_epcm1[page_table[2000]] == golden_epcm_2000 &&
               next_epcm1[page_table[2001]] == golden_epcm_2001 &&
               next_epcm1[page_table[2002]] == golden_epcm_2002 &&
               next_epcm1[page_table[2003]] == golden_epcm_2003 &&
               next_epcm1[page_table[2004]] == golden_epcm_2004 &&
               next_lp_state1[curr_lp] == golden_lpstate;
  */

  aux_next := next_epcm1[2000] == next_epcm2[2000] && 
         next_epcm1[2001] == next_epcm2[2001] && 
         next_epcm1[2002] == next_epcm2[2002] && 
         next_epcm1[2003] == next_epcm2[2003] && 
         next_epcm1[2004] == next_epcm2[2004] && 
         next_mem_secs1[2000] == next_mem_secs2[2000] && 
         next_mem_tcs1[2001] == next_mem_tcs2[2001] && 
         next_mem_reg1[2002] == next_mem_reg2[2002] && 
         next_lp_state1[curr_lp] == next_lp_state2[curr_lp] &&
         (forall i: physical_address :: (i < 2000 || i > 2004) ==> 
                                        (Epcm_enclavesecs(next_epcm1[i]) < 2000 || 
                                         Epcm_enclavesecs(next_epcm1[i]) > 2004));

  aux_next_const := next_mem_secs1[2000] == golden_secs &&
               next_mem_tcs1[2001] == golden_tcs &&
               next_epcm1[2000] == golden_epcm_2000 &&
               next_epcm1[2001] == golden_epcm_2001 &&
               next_epcm1[2002] == golden_epcm_2002 &&
               next_epcm1[2003] == golden_epcm_2003 &&
               next_epcm1[2004] == golden_epcm_2004 &&
               next_lp_state1[curr_lp] == golden_lpstate;

  assert (phi_next && aux_next && aux_next_const);
}


//Initial state setup
procedure {:inline 1} init() 
modifies epcm, lp_state, xstate, page_table, mem_reg, mem_tcs, mem_secs;
{
  havoc epcm; havoc lp_state; havoc xstate; havoc page_table;
  havoc mem_reg; havoc mem_tcs; havoc mem_secs; 

  assume (forall pa: physical_address :: epcm[pa] == Epcm(false, pt_reg, dummy_physical_address, dummy_linear_address)); 
  assume (forall lp: lp_id :: lp_state[lp] == Lp_state(false, dummy_physical_address, dummy_physical_address, dummy_lsrr, dummy_physical_address)); 
  assume (forall lp: lp_id :: xstate[lp] == dummy_xstate);
  assume (forall i : linear_address :: ((i != dummy_linear_address) ==> (page_table[i] == i && i != dummy_physical_address)) &&
                                        (i == dummy_linear_address ==> page_table[i] == dummy_physical_address));
}


function adversary_operation_choose(int): int;
function adversary_operation_ecreate_arg0(int): linear_address;
function adversary_operation_ecreate_arg1(int): secs_ty;
function adversary_operation_eadd_reg_arg0(int): linear_address;
function adversary_operation_eadd_reg_arg1(int): linear_address;
function adversary_operation_eadd_reg_arg2(int): data;
function adversary_operation_eadd_tcs_arg0(int): linear_address;
function adversary_operation_eadd_tcs_arg1(int): linear_address;
function adversary_operation_eadd_tcs_arg2(int): tcs_ty;
function adversary_operation_eremove_arg0(int): linear_address;
function adversary_operation_eextend_arg0(int): linear_address;
function adversary_operation_ereport_arg0(int): targetinfo_ty;
function adversary_operation_ereport_arg1(int): data;
function adversary_operation_einit_arg0(int): sigstruct_signed_ty;
function adversary_operation_einit_arg1(int): linear_address;
function adversary_operation_einit_arg2(int): einittoken_ty;
function adversary_operation_eenter_arg0(int): linear_address;
function adversary_operation_eresume_arg0(int): linear_address;

procedure {:inline 1} osvmm_adversary()
modifies mem_reg, mem_tcs, mem_secs, epcm, lp_state, xstate, page_table, curr_lp, arbitrary_write_count;
{
  var la: linear_address;
  var ereport_result : report_maced_ty; 
  var old_mem_reg : [physical_address] data;
  var arb: int;

  if (adversary_operation_choose(arb) == 0) {
    //no switch thread needed
    assume page_table[la] == Lp_state_cr_tcs_pa(lp_state[curr_lp]);
    call interrupt();
    call eresume_with_assumptions(la);
  } else if (adversary_operation_choose(arb) == 1) {
    //no switch thread needed
    assume page_table[la] == Lp_state_cr_tcs_pa(lp_state[curr_lp]); //capture which enclave needs to be resumed
    call interrupt();
    old_mem_reg := mem_reg;
    havoc mem_reg; assume (forall a: physical_address :: (is_epc_address(a)) ==> (mem_reg[a] == old_mem_reg[a]));
    call eresume_with_assumptions(la);
  } else if (adversary_operation_choose(arb) == 2) {
    call switch_thread(curr_lp + 1);
    old_mem_reg := mem_reg;
    havoc mem_reg; assume (forall a: physical_address :: (is_epc_address(a)) ==> (mem_reg[a] == old_mem_reg[a]));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 3) {
    call switch_thread(curr_lp + 1);
    call ecreate_with_assumptions(adversary_operation_ecreate_arg0(arb),
                                  adversary_operation_ecreate_arg1(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 4) {
    call switch_thread(curr_lp + 1);
    call eadd_tcs_with_assumptions(adversary_operation_eadd_tcs_arg0(arb),
                                   adversary_operation_eadd_tcs_arg1(arb),
                                   adversary_operation_eadd_tcs_arg2(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 5) {
    call switch_thread(curr_lp + 1);
    call eadd_reg_with_assumptions(adversary_operation_eadd_reg_arg0(arb),
                                   adversary_operation_eadd_reg_arg1(arb),
                                   adversary_operation_eadd_reg_arg2(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 6) {
    call switch_thread(curr_lp + 1);
    call eextend_with_assumptions(adversary_operation_eextend_arg0(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 7) {
    call switch_thread(curr_lp + 1);
    call eremove_with_assumptions(adversary_operation_eremove_arg0(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 8) {
    call switch_thread(curr_lp + 1);
    call einit_with_assumptions(adversary_operation_einit_arg0(arb),
                                adversary_operation_einit_arg1(arb),
                                adversary_operation_einit_arg2(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 9) {
    call switch_thread(curr_lp + 1);
    call eenter_with_assumptions(adversary_operation_eenter_arg0(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 10) {
    call switch_thread(curr_lp + 1);
    call eresume_with_assumptions(adversary_operation_eresume_arg0(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 11) {
    call switch_thread(curr_lp + 1);
    call ereport_result := 
         ereport_with_assumptions(adversary_operation_ereport_arg0(arb),
                                  adversary_operation_ereport_arg1(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 12) {
    havoc page_table;
  }
}

procedure {:inline 1} adversary_func()
modifies mem_reg, mem_tcs, mem_secs, epcm, lp_state, xstate, page_table, curr_lp, arbitrary_write_count;
{
  var la: linear_address;
  var ereport_result : report_maced_ty; 
  var old_mem_reg : [physical_address] data;
  var arb: int;

  if (adversary_operation_choose(arb) == 0) {
  } else if (adversary_operation_choose(arb) == 1) {
  } else if (adversary_operation_choose(arb) == 2) {
    call switch_thread(curr_lp + 1);
    old_mem_reg := mem_reg;
    havoc mem_reg; assume (forall a: physical_address :: (is_epc_address(a)) ==> (mem_reg[a] == old_mem_reg[a]));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 3) {
    call switch_thread(curr_lp + 1);
    call ecreate_with_assumptions(adversary_operation_ecreate_arg0(arb),
                                  adversary_operation_ecreate_arg1(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 4) {
    call switch_thread(curr_lp + 1);
    call eadd_tcs_with_assumptions(adversary_operation_eadd_tcs_arg0(arb),
                                   adversary_operation_eadd_tcs_arg1(arb),
                                   adversary_operation_eadd_tcs_arg2(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 5) {
    call switch_thread(curr_lp + 1);
    call eadd_reg_with_assumptions(adversary_operation_eadd_reg_arg0(arb),
                                   adversary_operation_eadd_reg_arg1(arb),
                                   adversary_operation_eadd_reg_arg2(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 6) {
    call switch_thread(curr_lp + 1);
    call eextend_with_assumptions(adversary_operation_eextend_arg0(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 7) {
  } else if (adversary_operation_choose(arb) == 8) {
    call switch_thread(curr_lp + 1);
    call einit_with_assumptions(adversary_operation_einit_arg0(arb),
                                adversary_operation_einit_arg1(arb),
                                adversary_operation_einit_arg2(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 9) {
    //call switch_thread(curr_lp + 1);
    //call eenter_with_assumptions(adversary_operation_eenter_arg0(arb));
    //call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 10) {
  } else if (adversary_operation_choose(arb) == 11) {
    call switch_thread(curr_lp + 1);
    call ereport_result := 
         ereport_with_assumptions(adversary_operation_ereport_arg0(arb),
                                  adversary_operation_ereport_arg1(arb));
    call switch_thread(curr_lp - 1);
  } else if (adversary_operation_choose(arb) == 12) {
    havoc page_table;
  }
}

//separate functions because I don't want assumptions from adversary_operation to impact arguments to enclave operations
function enclave_operation_choose(int): int;
function enclave_operation_ereport_arg0(int): targetinfo_ty;
function enclave_operation_ereport_arg1(int): data;
function enclave_operation_egetkey_arg0(int): keyrequest_ty;
function enclave_operation_write_arg0(int): linear_address;
function enclave_operation_write_arg1(int): data;
function enclave_operation_read_arg0(int): linear_address;

const EREPORT: int; axiom EREPORT == 0;
const EGETKEY: int; axiom EGETKEY == 1;
const WRITE : int; axiom WRITE == 2;
const READ : int; axiom READ == 3;

//Need this axiom to prevent the return variables from getting bogus values
axiom (forall i: int :: {enclave_operation_choose(i)} 
  enclave_operation_choose(i) == EREPORT ||
  enclave_operation_choose(i) == EGETKEY ||
  enclave_operation_choose(i) == WRITE ||
  enclave_operation_choose(i) == READ
);

procedure {:inline 1} enclave_operation(index: int) 
returns (ereport_result: report_maced_ty, egetkey_result: key_ty, read_result: data)
modifies mem_reg, mem_secs, mem_tcs, arbitrary_write_count;
{
  var tmp: key_ty;
  if (enclave_operation_choose(index) == EREPORT) {
    call ereport_result := ereport_with_assumptions(
                             enclave_operation_ereport_arg0(index), 
                             enclave_operation_ereport_arg1(index)
                           ); 
  }
  else if (enclave_operation_choose(index) == EGETKEY) {
    call egetkey_result := egetkey_with_assumptions(
                             enclave_operation_egetkey_arg0(index));
  }
  else if (enclave_operation_choose(index) == WRITE) {
    call write(enclave_operation_write_arg0(index), 
               enclave_operation_write_arg1(index));
  }
  else if (enclave_operation_choose(index) == READ) {
    assume Lp_state_cr_enclave_mode(lp_state[curr_lp]); 
    //USE THIS FOR integrity_proof()
    assume in_register_range( enclave_operation_read_arg0(index), Lp_state_cr_elrange(lp_state[curr_lp])) && 
           !in_ssa_range(enclave_operation_read_arg0(index), 
                         mem_tcs[Lp_state_cr_tcs_pa(lp_state[curr_lp])], 
                         mem_secs[Lp_state_cr_active_secs(lp_state[curr_lp])]);
    //use this for adversary_havoc_reduction_proof()
    /*
    assume !in_ssa_range(enclave_operation_read_arg0(index), 
                         mem_tcs[Lp_state_cr_tcs_pa(lp_state[curr_lp])], 
                         mem_secs[Lp_state_cr_active_secs(lp_state[curr_lp])]);
    */
    call read_result := read(enclave_operation_read_arg0(index)); 
  }
}


