; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
(set-logic ALL)
(set-option :incremental true)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (<= b 0.25))
(assert (= (- b a) 3.0))
(assert (or (> (* 2 b) 0.0) (= (/ 1.0 b) 3.0)))
(check-sat)
(push)
(check-sat)
(pop)
(assert (>= (* 3.0 a) 1.0))
(check-sat)
