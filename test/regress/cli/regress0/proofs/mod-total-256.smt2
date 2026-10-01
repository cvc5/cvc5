; EXPECT: unsat
; DISABLE-TESTER: alethe
(set-logic ALL)
(declare-fun index () Int)
(assert (not
(= (mod_total (mod_total index 256) 256) (mod_total index 256))))
(check-sat)
