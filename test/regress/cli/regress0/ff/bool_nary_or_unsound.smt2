; REQUIRES: cocoa
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
(declare-fun a () Bool)
(declare-fun b () Bool)
(declare-fun c () Bool)
(declare-fun d () Bool)
(declare-fun e () Bool)
(assert (not (=
  (or a b c d e)
  (not (= (ff.add
    (ite a #f1m5 #f0m5)
    (ite b #f1m5 #f0m5)
    (ite c #f1m5 #f0m5)
    (ite d #f1m5 #f0m5)
    (ite e #f1m5 #f0m5)
  ) #f0m5
  ))
)))
(check-sat)
