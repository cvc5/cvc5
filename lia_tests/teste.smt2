(set-logic QF_LIA)

(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (= (+ (+ (* 11 z) (+ (* 9 x) (- 19))) (* 3 y)) 1))
(check-sat)
