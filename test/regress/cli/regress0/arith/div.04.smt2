(set-logic QF_NRA)
(set-info :smt-lib-version 2.6)
(set-info :status unsat)
(declare-fun x () Real)
(declare-fun y () Real)
(declare-fun n () Real)

(assert (not (=> (= x y) (= (/ x n) (/ y n)))))
(assert (<= n 0))
(assert (>= n 0))

(check-sat)
