
implementation measure_mem_self_composed(
    /* meas */ m1_in, m2_in : measurement_t,
    /* addr */ paddr1 : wap_addr_t, paddr2 : wap_addr_t, 
    /* mem  */ mem1, mem2 : mem_t,
    /* len  */ len : wap_addr_t)
  returns (m1 : measurement_t, m2 : measurement_t)
{
  var pa1, pa2 : wap_addr_t;
  var ind      : wap_addr_t;
  var w1, w2   : word_t;
  var sum      : wap_addr_t;
  
  m1 := m1_in;
  m2 := m2_in;

  ind := k0_wap_addr_t;
  while (LT_wapa(ind, len))
    invariant LE_wapa(ind, len);
    invariant ((forall i : wap_addr_t :: 
        (LT_wapa(i, ind) ==> mem1[offset_paddr(paddr1, i)] == mem2[offset_paddr(paddr2, i)])) &&
        m1_in == m2_in)
      ==> (m1 == m2);
    invariant ((exists i : wap_addr_t :: 
        (LT_wapa(i, ind) && mem1[offset_paddr(paddr1, i)] != mem2[offset_paddr(paddr2, i)])) ||
        m1_in != m2_in)
      ==> (m1 != m2);
  {
    m1 := update_digest(word2int(mem1[offset_paddr(paddr1, ind)]), m1);
    m2 := update_digest(word2int(mem2[offset_paddr(paddr2, ind)]), m2);
    ind := PLUS_wapa(ind, k1_wap_addr_t);
  }
}
