; REQUIRES: unrestricted-mode
; COMMAND-LINE: --term-sort-overload
; EXPECT: unsat
; External proof checking does not support overloading a term and a sort
; with the same name (U).
; DISABLE-TESTER: cpc
(set-logic ALL)
(declare-sort U 0)
(declare-fun U () U)
(assert (not (= U U)))
(check-sat)
