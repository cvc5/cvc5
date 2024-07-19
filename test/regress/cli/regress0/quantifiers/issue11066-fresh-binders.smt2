; COMMAND-LINE: --fresh-binders
; EXPECT: unsat
; DISABLE-TESTER: proof
(set-logic ALL)
(assert (exists ((x Real))
          (let ((?y x))
          (and (<= 0 x) (exists ((x Real)) (forall ((v Real)) (> 0 ?y)))))))
(check-sat)
