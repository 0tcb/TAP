
implementation init_cache()
{
  var ind : cache_set_index_t;
  var way : cache_way_index_t;
  ind := 0;

  while (ind < kmax_cache_set_index_t)
    invariant (forall i : cache_set_index_t, w : cache_way_index_t :: 
        (i >= 0 && i < ind && valid_cache_way_index(w)) ==> !cache_valid_map[i, w]);
  {
    way := 0;
    while (way < kmax_cache_way_index_t) 
      invariant (forall i : cache_set_index_t, w : cache_way_index_t :: 
        ((i >= 0 && i < ind && valid_cache_way_index(w)) || (i == ind && w >= 0 && w < way)) ==>
            !cache_valid_map[i, w]);
    {
      cache_valid_map[ind, way] := false;
      way := way + 1;
    }
    ind := ind + 1;
  }
}

implementation query_cache(pa : wap_addr_t, repl_way : cache_way_index_t)
  returns (hit : bool, hit_way : cache_way_index_t)
{
  var set : cache_set_index_t;
  var tag : cache_tag_t;
  var way : cache_way_index_t;

  set := paddr2set(pa);
  tag := paddr2tag(pa);

  way := 0;
  hit := false;
  while (!hit && way < kmax_cache_way_index_t)
    invariant (way >= 0);
    invariant (way <= kmax_cache_way_index_t);
    invariant hit ==> (cache_valid_map[set, hit_way] && cache_tag_map[set, hit_way] == tag);
    invariant 
      (!hit <==>
        (forall w : cache_way_index_t ::
          (w >= 0 && w < way) ==>
            (!cache_valid_map[set, w] || cache_tag_map[set, w] != tag)));
  {
    if (cache_valid_map[set, way] && cache_tag_map[set, way] == tag) {
      hit := true;
      hit_way := way;
    }
    way := way + 1;
  }
  // do the replacement.
  if (!hit) {
      cache_valid_map[set, repl_way] := true;
      cache_tag_map[set, repl_way] := tag;
  }
}
