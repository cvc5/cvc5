; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(set-option :proof-check eager)
(set-option :unsat-cores-mode sat-proof)
(assert (<= real.pi (sec 0.0)))
(check-sat)
