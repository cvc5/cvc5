; COMMAND-LINE: --strings-exp
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun rrck_19 () (Seq Real))
(assert (not (= rrck_19 (str.update rrck_19 2 rrck_19))))
(check-sat)
