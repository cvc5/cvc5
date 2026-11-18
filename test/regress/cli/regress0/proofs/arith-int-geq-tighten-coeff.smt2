; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(declare-const x Int)
(assert (not (= (>= (* (/ 1 3) (to_real x)) (/ 3 2)) (>= x 5))))
(check-sat)
