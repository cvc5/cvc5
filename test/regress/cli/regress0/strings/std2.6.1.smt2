; COMMAND-LINE: --strings-exp --lang=smt2.6
; EXPECT: sat
(set-logic QF_UFSLIA)
(set-info :status sat)
(declare-fun x () String)
(assert (str.in_re x (str.to_re "A")))
(declare-fun y () Int)
(assert (= (str.to_int (str.from_int y)) y))
(check-sat)
