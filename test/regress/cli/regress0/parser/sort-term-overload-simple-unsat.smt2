; COMMAND-LINE: --sort-term-overload
; EXPECT: unsat
; DISABLE-TESTER: cpc
(set-logic ALL)
(declare-sort U 0)
(declare-fun U () U)
(assert (not (= U U)))
(check-sat)
