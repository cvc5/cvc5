; REQUIRES: cocoa
; EXPECT: unsat
; Tests the ff rewriter
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
; all disjuncts should be false
(declare-fun x () (_ FiniteField 17))
(assert (= (ff.mul x x) x))
(assert (not (= x #f1m17)))
(assert (not (= x #f0m17)))
(check-sat)
