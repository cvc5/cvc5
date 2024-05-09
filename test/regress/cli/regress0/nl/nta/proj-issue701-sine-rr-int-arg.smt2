; EXPECT: unsat
;; Logic not supported in Alethe
; DISABLE-TESTER: alethe
(set-logic ALL)
(check-sat-assuming ((<= 0.0 (sin (+ 1.0 real.pi)))))
