; DISABLE-TESTER: alethe
; COMMAND-LINE: --check-proofs
; EXPECT: unsat
(set-logic ALL)
(define-fun i () Real (/ 0.0 0))
(assert (forall ((l Real)) (and false (= i 0))))
(check-sat)
