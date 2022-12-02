BOOGIEOPT:=/proverOpt:O:smt.relevancy=0 /proverOpt:O:smt.case_split=0 /errorLimit:1
BUILD=build

SGX_PROOF_TARGET=$(BUILD)/SGXProof.xml
all: $(SGX_PROOF_TARGET)

$(SGX_PROOF_TARGET): Hardware/sgx.bpl Proof.bpl
	$(BOOGIE) /xml:$@ $(BOOGIEOPT) $^

clean:
	rm -f $(BUILD)/*.xml

.PHONY: clean
