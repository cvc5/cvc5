(set-logic QF_LIA)

(declare-const x Int)
(declare-const y Int)
(assert (<= (+ x (* 2 y)) 1))
(check-sat)
