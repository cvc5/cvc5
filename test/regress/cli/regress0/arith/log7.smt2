;EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const x Int)
(assert (< (int.log2 x) 0))
(check-sat)
