; COMMAND-LINE: --strings-exp --lang=smt2.6.1
; EXPECT: sat
(set-logic QF_UFSLIA)
(set-info :status sat)
(declare-fun x () String)
(assert (str.in-re x (str.to-re "A")))
(declare-fun y () Int)
(assert (= (str.to-int (str.from-int y)) y))
(check-sat)
