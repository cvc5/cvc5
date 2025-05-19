; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-const a (Array RoundingMode Int))
(declare-const b (Array RoundingMode Int))
(assert false)
(assert (= a b))
(check-sat)
