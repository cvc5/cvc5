;REQUIRES: poly
;EXPECT: sat
(set-logic QF_NRA)
(declare-fun a () Real)
(assert (= (* a a) 2))
(check-sat)
