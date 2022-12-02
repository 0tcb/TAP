BOOGIEOPT:=/proverOpt:O:smt.relevancy=0 /proverOpt:O:smt.case_split=0 /errorLimit:1

BUILD=build
CACHE_TARGET:=$(BUILD)/Cache.xml

COMMON_FILES:=Types.bpl
CACHE_FILES:=Cache.bpl CacheImpl.bpl

all: $(CACHE_TARGET)
$(CACHE_TARGET): $(COMMON_FILES) $(CACHE_FILES)
	$(BOOGIE) $(BOOGIEOPT) /xml:$@ $^

clean:
	rm -f build/*.xml

.PHONY: clean
