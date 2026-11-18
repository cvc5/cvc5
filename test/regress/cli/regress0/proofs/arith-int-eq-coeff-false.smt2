; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(declare-const x Int)
(assert (not (= (= (/ 1 2) (* (/ 1 3) (to_real x))) false)))
(check-sat)
