#! /bin/bash

#COMMON=Common
#AP=AbstractPlatform
#cpu="$COMMON/Types.bpl $COMMON/Cache.bpl $COMMON/CacheImpl.bpl $AP/Types.bpl $AP/CPU.bpl $AP/CPUImpl.bpl $AP/Measure.bpl"
#tapint="$AP/ProofCommon.bpl $AP/ImplCommon.bpl $AP/IntegrityProof.bpl"
#tapmeas="$AP/MeasurementProof.bpl"
#tapconf="$AP/CacheConfidentialityProof.bpl $AP/ConfidentialityProof.bpl $AP/MemConfidentialityProof.bpl $AP/PTConfidentialityProof.bpl"
#
#wc -l $cpu
#boogie /noResolve /print:/tmp/tmp.bpl $cpu
#grep '\<procedure\>' /tmp/tmp.bpl | wc -l
#grep '\<function\>' /tmp/tmp.bpl | wc -l
#grep '\<invariant\>\|\<ensures\>\|<requires\>\|\<assume\>\|\<assert\>' /tmp/tmp.bpl | wc -l
#
#wc -l $tapint
#boogie /noResolve /print:/tmp/tmp.bpl $tapint
#grep '\<procedure\>' /tmp/tmp.bpl | wc -l
#grep '\<function\>' /tmp/tmp.bpl | wc -l
#grep '\<invariant\>\|\<ensures\>\|<requires\>\|\<assume\>\|\<assert\>' /tmp/tmp.bpl | wc -l
#
#wc -l $tapmeas
#boogie /noResolve /print:/tmp/tmp.bpl $tapmeas
#grep '\<procedure\>' /tmp/tmp.bpl | wc -l
#grep '\<function\>' /tmp/tmp.bpl | wc -l
#grep '\<invariant\>\|\<ensures\>\|<requires\>\|\<assume\>\|\<assert\>' /tmp/tmp.bpl | wc -l
#
#wc -l $tapconf
#boogie /noResolve /print:/tmp/tmp.bpl $tapconf
#grep '\<procedure\>' /tmp/tmp.bpl | wc -l
#grep '\<function\>' /tmp/tmp.bpl | wc -l
#grep '\<invariant\>\|\<ensures\>\|<requires\>\|\<assume\>\|\<assert\>' /tmp/tmp.bpl | wc -l

mmu="Sanctum/MMU/MMU.bpl Sanctum/MMU/Common/Common.bpl Sanctum/MMU/AbstractSanctumMMU/AbstractRISCVMMU/AbstractRISCVMMU.bpl Sanctum/MMU/AbstractSanctumMMU/AbstractSanctumMMU.bpl Sanctum/MMU/ConcreteSanctumMMU/ConcreteRISCVMMU/ConcreteRISCVMMU.bpl Sanctum/MMU/ConcreteSanctumMMU/ConcreteSanctumMMU.bpl Sanctum/MMU/AbstractSanctumMMU/AbstractRISCVMMU/AbstractRISCVMMUImpl.bpl Sanctum/MMU/AbstractSanctumMMU/AbstractSanctumMMUImpl.bpl Sanctum/MMU/ConcreteSanctumMMU/ConcreteRISCVMMU/ConcreteRISCVMMUImpl.bpl Sanctum/MMU/ConcreteSanctumMMU/ConcreteSanctumMMUImpl.bpl Sanctum/MMU/MMUImpl.bpl"
wc -l $mmu
boogie /noResolve /print:/tmp/tmp.bpl $mmu
grep '\<procedure\>' /tmp/tmp.bpl | wc -l
grep '\<function\>' /tmp/tmp.bpl | wc -l
grep '\<invariant\>\|\<ensures\>\|<requires\>\|\<assume\>\|\<assert\>' /tmp/tmp.bpl | wc -l

mmuref="Sanctum/MMU/MMUProof.bpl"
wc -l $mmuref
boogie /noResolve /print:/tmp/tmp.bpl $mmuref
grep '\<procedure\>' /tmp/tmp.bpl | wc -l
grep '\<function\>' /tmp/tmp.bpl | wc -l
grep '\<invariant\>\|\<ensures\>\|<requires\>\|\<assume\>\|\<assert\>' /tmp/tmp.bpl | wc -l

monitor="Sanctum/Common/Types.bpl Sanctum/Common/Prelude.bpl Sanctum/Common/Machine.bpl Sanctum/Utils/Utils.bpl Sanctum/Utils/UtilsImpl.bpl Sanctum/CPU/CPU.bpl Sanctum/Monitor/Monitor.bpl"
wc -l $monitor
boogie /noResolve /print:/tmp/tmp.bpl $monitor
grep '\<procedure\>' /tmp/tmp.bpl | wc -l
grep '\<function\>' /tmp/tmp.bpl | wc -l
grep '\<invariant\>\|\<ensures\>\|<requires\>\|\<assume\>\|\<assert\>' /tmp/tmp.bpl | wc -l

srp="SanctumRefinementProof.bpl"
wc -l $srp
boogie /noResolve /print:/tmp/tmp.bpl $srp
grep '\<procedure\>' /tmp/tmp.bpl | wc -l
grep '\<function\>' /tmp/tmp.bpl | wc -l
grep '\<invariant\>\|\<ensures\>\|<requires\>\|\<assume\>\|\<assert\>' /tmp/tmp.bpl | wc -l
