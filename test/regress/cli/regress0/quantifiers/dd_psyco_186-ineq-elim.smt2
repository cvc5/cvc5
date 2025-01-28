; EXPECT: unsat
(set-logic ALL)
(declare-fun W () Bool)
(assert (forall ((S Int) (S1 Int)) (or (not (and (>= 1 1) (>= S 0))) (= S (+ (- 1) (ite W 0 1))))))
(assert W)
(check-sat)
