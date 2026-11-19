; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (not (= (>= (+ (* (/ 1 3) (to_real x)) (* (/ 2 3) (to_real y))) (/ 3 2)) (>= (+ x (* 2 y)) 5))))
(check-sat)
