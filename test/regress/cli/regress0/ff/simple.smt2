; REQUIRES: cocoa
; EXPECT: unsat
; Tests the ff rewriter
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
; all disjuncts should be false
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(assert (not (=
  (or a b c)
  (not (= (ff.add
    (ite a #f1m5 #f0m5)
    (ite b #f1m5 #f0m5)
    (ite c #f1m5 #f0m5)
  ) #f0m5
  ))
)))
(check-sat)
