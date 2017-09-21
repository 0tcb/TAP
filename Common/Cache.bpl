// -------------------------------------------------------------------- //
// cache state                                                          //
// -------------------------------------------------------------------- //

var cache_valid_map   : cache_valid_map_t;
var cache_tag_map     : cache_tag_map_t;

procedure init_cache();
  modifies cache_valid_map;
  ensures (forall i : cache_set_index_t, w : cache_way_index_t ::
            (valid_cache_set_index(i) && valid_cache_way_index(w)) ==> !cache_valid_map[i, w]);

procedure query_cache(pa : wap_addr_t, repl_way : cache_way_index_t)
  returns (hit : bool, hit_way : cache_way_index_t);

  modifies cache_valid_map, cache_tag_map;

  // must return a valid way.
  requires (valid_cache_way_index(repl_way));

  // set hit status.
  ensures !hit <==> (forall w : cache_way_index_t :: 
                        valid_cache_way_index(w) ==> 
                            (!old(cache_valid_map)[paddr2set(pa), w] ||
                              old(cache_tag_map[paddr2set(pa), w]) != paddr2tag(pa)));
  ensures (hit <==> (exists w : cache_way_index_t ::
                      valid_cache_way_index(w)               && 
                      old(cache_valid_map)[paddr2set(pa), w] && 
                      old(cache_tag_map)[paddr2set(pa), w] == paddr2tag(pa)));
  // do replacement if necessary.
  ensures (if !hit 
              then cache_valid_map[paddr2set(pa), repl_way]
              else cache_valid_map[paddr2set(pa), hit_way]);
  ensures (if !hit 
              then cache_tag_map[paddr2set(pa), repl_way] == paddr2tag(pa)
              else cache_tag_map[paddr2set(pa), hit_way]  == paddr2tag(pa));

  // and no other lines are affected.
  ensures !hit ==>
          (forall i : cache_set_index_t, w : cache_way_index_t :: 
            (i != paddr2set(pa) || w != repl_way) ==> cache_valid_map[i, w] == old(cache_valid_map)[i, w]);
  ensures !hit ==>
          (forall i : cache_set_index_t, w : cache_way_index_t :: 
            (i != paddr2set(pa) || w != repl_way) ==> cache_tag_map[i, w] == old(cache_tag_map)[i, w]);

  ensures hit ==> (cache_valid_map == old(cache_valid_map) && cache_tag_map == old(cache_tag_map));
