; COMMAND-LINE: --solve-bv-as-int=sum --bvand-integer-granularity=1
; COMMAND-LINE: --solve-bv-as-int=bitwise --bvand-integer-granularity=1
; EXPECT: unsat
; unsat-core times out on some builds
; DISABLE-TESTER: unsat-core
(set-logic QF_BV)
(declare-fun T4_180 () (_ BitVec 32))
(assert (and 
(= (bvmul T4_180 (_ bv1056 32)) (_ bv0 32)) 
(not (= (bvmul T4_180 (_ bv1408 32)) (_ bv0 32))) 
)
)
(check-sat)
