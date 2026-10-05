; REQUIRES: unrestricted-mode
; COMMAND-LINE: --fresh-binders
; EXPECT: unsat
; --fresh-binders is not supported with proofs or unsat cores.
; DISABLE-TESTER: proof
; DISABLE-TESTER: unsat-core
(set-logic ALL)
(assert (exists ((x Real))
          (let ((?y x))
          (and (<= 0 x) (exists ((x Real)) (forall ((v Real)) (> 0 ?y)))))))
(check-sat)
