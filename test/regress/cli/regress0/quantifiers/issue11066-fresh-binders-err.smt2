; DISABLE-TESTER: dump
; REQUIRES: no-competition
; EXPECT-ERROR: Must construct fresh variable for x since this symbol occurs in a let term that is present in the current context. Set fresh-binders to true to avoid this warning.
; EXPECT: unsat
(set-logic ALL)
(assert (exists ((x Real))
          (let ((?y x))
          (and (<= 0 x) (exists ((x Real)) (forall ((v Real)) (> 0 ?y)))))))
(check-sat)
