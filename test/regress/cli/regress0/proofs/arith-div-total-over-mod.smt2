; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic QF_NIA)
(declare-const x Int)
(assert (not (= (div (mod x 5) 5) 0)))
(check-sat)
