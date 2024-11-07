; DISABLE-TESTER: dump
; DISABLE-TESTER: alethe
; DISABLE-TESTER: cpc
; REQUIRES: no-competition
; EXPECT-ERROR: Constructing a fresh variable for x since this symbol occurs in a let term that is present in the current context. Set fresh-binders to true or use -q to avoid this warning.
; EXPECT: unsat
(set-logic ALL)
(assert (exists ((x Real))
          (let ((?y x))
          (and (<= 0 x) (exists ((x Real)) (forall ((v Real)) (> 0 ?y)))))))
(check-sat)
