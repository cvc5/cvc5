; REQUIRES: unrestricted-mode
; COMMAND-LINE: --bv-abstraction --produce-unsat-cores
; EXPECT: unsat
; Proof testing is disabled because it switches to --bv-solver=bitblast-internal,
; which does not support the bit-vector abstraction exercised by this test.
; DISABLE-TESTER: proof
; Ported from Bitwuzla test/regress/solver/abstract/unsatcore1.smt2
(set-logic BV)
(set-info :status unsat)
(declare-const x Bool)
(declare-const y Bool)
(assert (= (distinct true x) (and x (exists ((x Bool)) true))))
(check-sat)
