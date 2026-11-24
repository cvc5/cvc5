; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (str.<= x x) true)))
(check-sat)
