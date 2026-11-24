; DISABLE-TESTER: alethe
; EXPECT: unsat
(set-logic ALL)
(declare-const x String)
(declare-const y String)
(declare-const n Int)
(assert (not (= (str.indexof (str.substr x n 1) x 1) (- 1))))
(check-sat)
