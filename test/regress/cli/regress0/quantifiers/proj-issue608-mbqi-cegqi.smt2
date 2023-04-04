; EXPECT: unknown

; Benchmark unknown due to cegqi-all taking ownership; solvable with finite-model-find.

(set-logic ALL)
(set-option :mbqi true)
(set-option :cegqi-all true)
(declare-sort u 0)
(declare-const x u)
(assert (forall ((_x u)) (= _x x)))
(check-sat)
