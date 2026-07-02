; EXPECT: unsat
(set-logic QF_NIA)
(set-info :status unsat)
(declare-fun x () Int)
(declare-fun y () Int)

(assert (> x 0))
(assert (< 0 (mod (int.pow2 x) 2)))

(check-sat)
