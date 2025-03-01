; EXPECT: unsat
(set-logic ANRA)
(declare-fun r3 () Real)
(declare-fun r4 () Real)
(declare-fun arr () (Array Real Real))
(assert (and (= r3 (* r4 r3)) (= (* r4 r4) (- (select arr r4)))))
(assert (and (> r3 1.0) (= 1.0 (select arr 1.0))))
(check-sat)
