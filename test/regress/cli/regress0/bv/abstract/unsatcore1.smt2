; COMMAND-LINE: --bv-abstraction --produce-unsat-cores
; EXPECT: unsat
; DISABLE-TESTER: proof
; Ported from Bitwuzla test/regress/solver/abstract/unsatcore1.smt2
(set-logic BV)
(set-info :status unsat)
(declare-const x Bool)
(declare-const y Bool)
(assert (= (distinct true x) (and x (exists ((x Bool)) true))))
(check-sat)
