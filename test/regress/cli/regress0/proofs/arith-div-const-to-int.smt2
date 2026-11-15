; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (not (= (/ (- 3) y) (/ (- 3.0) (to_real y)))))
(check-sat)
