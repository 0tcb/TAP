
function wap_addr2int(va : wap_addr_t) : int;
axiom (forall v1, v2 : wap_addr_t :: (v1 != v2) ==> (wap_addr2int(v1) != wap_addr2int(v2)));
axiom (forall w : wap_addr_t :: wap_addr2int(w) >= 0 && wap_addr2int(w) <= kmax_wap_addr_t_as_int);

function offset_paddr(base : wap_addr_t, i : wap_addr_t) : wap_addr_t { PLUS_wapa(base, i) }

procedure measure_mem_self_composed(
    /* meas */ m1_in, m2_in : measurement_t,
    /* addr */ paddr1 : wap_addr_t, paddr2 : wap_addr_t, 
    /* mem  */ mem1, mem2 : mem_t,
    /* len  */ len : wap_addr_t)
  returns (m1 : measurement_t, m2 : measurement_t);
  ensures ((forall i : wap_addr_t :: 
            (LT_wapa(i, len) ==> 
              mem1[offset_paddr(paddr1, i)] == mem2[offset_paddr(paddr2, i)])) &&
           m1_in == m2_in)
    <==> (m1 == m2);
  ensures ((exists i : wap_addr_t :: 
            (LT_wapa(i, len) && 
              mem1[offset_paddr(paddr1, i)] != mem2[offset_paddr(paddr2, i)])) ||
           m1_in != m2_in)
    <==> (m1 != m2);

procedure {:inline 1} measure_mem(
    /* meas */ m_in  : measurement_t,
    /* addr */ paddr : wap_addr_t,
    /* mem  */ mem   : mem_t,
    /* len  */ len   : wap_addr_t
)
    returns (m : measurement_t)
{
    var m1, m2 : measurement_t;
    call m1, m2 := measure_mem_self_composed(m_in, m_in, paddr, paddr, mem, mem, len);
    assert (m1 == m2);
    m := m1;
}
