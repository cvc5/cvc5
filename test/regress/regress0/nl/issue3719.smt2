; REQUIRES: poly
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun a () Real)
(assert (= (* 4 a a) 9))
(check-sat)
