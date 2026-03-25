; EXPECT: unsat
(set-logic QF_ALL)
(declare-const p Int)
(declare-const u Int)
(assert (> (mod (+ (* u (ite (= p 4) (* 4 p) 0)) (* p ((_ iand 4) p u) (ite (= p 0) (mod_total 0 u) (ite (= p 4) (* 4 p) 0)))) 4) 0))
(check-sat)
