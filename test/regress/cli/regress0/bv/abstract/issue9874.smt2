; REQUIRES: unrestricted-mode
; COMMAND-LINE: --bv-abstraction
; EXPECT: unsat
; Proof testing is disabled because it switches to --bv-solver=bitblast-internal,
; which does not support the bit-vector abstraction exercised by this test.
; DISABLE-TESTER: proof
(set-logic QF_BV)
(declare-const a (_ BitVec 64))
(assert (= a (bvurem (bvnot a) a)))
(check-sat)
