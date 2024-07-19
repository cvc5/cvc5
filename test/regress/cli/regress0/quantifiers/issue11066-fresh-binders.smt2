; EXPECT: unsat
; DISABLE-TESTER: alf
(set-logic ALL)
(assert (exists ((x Real))
          (let ((?y x))
          (and (<= 0 x) (exists ((x Real)) (forall ((v Real)) (> 0 ?y)))))))
(check-sat)
