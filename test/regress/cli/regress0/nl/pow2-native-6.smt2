; EXPECT: unsat
(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (<= 0 x))
(assert (distinct 0 (div x (int.pow2 x))))

(check-sat)
