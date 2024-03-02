; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(assert false)
(assert (<= real.pi (sec real.pi)))
(check-sat)
