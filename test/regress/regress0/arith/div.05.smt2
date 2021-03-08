; EXPECT: sat
(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :status sat)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun n () Real)

(assert (= (/ x n) 0))
(assert (= (/ y n) 1))

(check-sat)
