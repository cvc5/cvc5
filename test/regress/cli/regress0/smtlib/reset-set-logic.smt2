; EXPECT: sat
; EXPECT: sat
(set-logic QF_LRA)
(declare-const x Real)
(assert (= x (- 2.5)))
(check-sat)

(reset)

(set-logic QF_LIA)
(declare-const x Int)
(assert (= x 2))
(check-sat)
