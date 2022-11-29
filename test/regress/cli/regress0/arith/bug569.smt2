; EXPECT: unsat
; DISABLE-TESTER: unsat-core
; timeout with unsat cores
(set-logic QF_AUFLIRA)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-info :status unsat)
(declare-fun v1 () Int)
(declare-fun v3 () Int)
(declare-fun v5 () Real)
(assert (= (to_real v1) (+ (to_real v3) v5)))
(assert (< v5 1.0))
(assert (> v5 0.0))
(check-sat)
(exit)
