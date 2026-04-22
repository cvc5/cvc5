; EXPECT: unsat
(set-logic ALL)
(declare-const t Int)
(declare-const a Int)
(assert (ite (= 0 (/ t 0)) (is_int (/ (to_real 2) (to_real t))) (<= t 2)))
(assert (> (+ t a) 5))
(assert (ite (< 0 (to_real a)) (is_int (/ (to_real 3) (to_real a))) true))
(check-sat)
