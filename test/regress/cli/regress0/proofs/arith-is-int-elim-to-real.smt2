; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic QF_LIRA)
(declare-const x Int)
(assert (not (is_int (to_real x))))
(check-sat)
