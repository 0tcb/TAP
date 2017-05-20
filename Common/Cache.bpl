// -------------------------------------------------------------------- //
// cache state                                                          //
// -------------------------------------------------------------------- //

var cache_valid_map   : cache_valid_map_t;
var cache_tag_map     : cache_tag_map_t;

procedure init_cache();
  modifies cache_valid_map;
  ensures (forall i : cache_set_index_t :: !cache_valid_map[i]);

procedure query_cache(pa : wap_addr_t)
  returns (hit : bool);

  modifies cache_valid_map, cache_tag_map;

  // set hit status.
  ensures hit == (old(cache_valid_map)[paddr2set(pa)] && 
                  old(cache_tag_map)[paddr2set(pa)] == paddr2tag(pa));
  // do replacement if necessary.
  ensures cache_valid_map[paddr2set(pa)];
  ensures cache_tag_map[paddr2set(pa)] == paddr2tag(pa);

  // and no other lines are affected.
  ensures (forall t : cache_set_index_t :: 
            t != paddr2set(pa) ==> cache_valid_map[t] == old(cache_valid_map)[t]);
  ensures (forall t : cache_set_index_t :: 
            t != paddr2set(pa) ==> cache_tag_map[t] == old(cache_tag_map)[t]);

