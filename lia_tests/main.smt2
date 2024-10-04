(set-logic QF_LIA)

(declare-const x Int)
(declare-const y Int)
;(declare-const z Int)
(assert (= (+ x (* 2 y)) 1))
;(assert (= (+ (+ (* 3 z) (+ (* 7 x) 5)) (* 2 y)) 1))
(check-sat)
