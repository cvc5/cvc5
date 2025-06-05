; COMMAND-LINE: --term-sort-overload
; EXPECT: unsat
; DISABLE-TESTER: cpc
; DISABLE-TESTER: lfsc
(set-logic ALL)
(declare-sort U 0)
(declare-fun U () U)
(assert (not (= U U)))
(check-sat)
