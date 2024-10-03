(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)

(assert (= (mod (+ x (* 2 y)) 2) 1))
(check-sat)
