; EXPECT: sat
(set-logic QF_LIRA)
(declare-const i1 Int)
(declare-const r2 Real)
(declare-const i13 Int)
(assert (is_int (- 0.0 0.0 0.0 r2 (to_real (abs i1)))))
(assert (< (to_real (to_int (to_real i13))) (- r2) 0.0 (to_real 60)))
(check-sat)
