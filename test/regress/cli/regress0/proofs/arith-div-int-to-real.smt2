; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic QF_NIRA)
(declare-const x Int)
(declare-const y Int)
(assert (not (= (/ x y) (/ (to_real x) (to_real y)))))
(check-sat)
