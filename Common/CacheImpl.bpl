
implementation init_cache()
{
  var ind : cache_set_index_t;
  ind := k0_cache_set_index_t;

  while (LT_csi(ind, kmax_cache_set_index_t))
    invariant (forall i : cache_set_index_t :: LT_csi(i, ind) ==> !cache_valid_map[i]);
  {
    cache_valid_map[ind] := false;
    ind := PLUS_csi(ind, k1_cache_set_index_t);
  }
  cache_valid_map[ind] := false;
}

implementation query_cache(pa : wap_addr_t)
  returns (hit : bool)
{
  var set : cache_set_index_t;
  var tag : cache_tag_t;

  set := paddr2set(pa);
  tag := paddr2tag(pa);
  hit := cache_valid_map[set] && cache_tag_map[set] == tag;
  if (!hit) {
    // do the replacement.
    cache_valid_map[set] := true;
    cache_tag_map[set] := tag;
  }
}
