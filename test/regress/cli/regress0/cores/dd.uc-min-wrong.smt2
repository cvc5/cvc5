; COMMAND-LINE: --minimal-unsat-cores
; EXPECT: unsat
(set-logic ALL)
(define-fun a ((b!b Int) (b!b2 Int)) Bool false)
(assert (a 0 0))
(check-sat)
