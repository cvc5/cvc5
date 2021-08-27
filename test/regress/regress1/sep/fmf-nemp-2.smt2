; COMMAND-LINE: --finite-model-find --no-check-models
; EXPECT: sat
(set-logic ALL)
(declare-sort U 0)
(declare-heap (U Int))
(declare-fun u1 () U)
(declare-fun u2 () U)
(assert (not (= u1 u2)))
(assert (forall ((x U)) (=> (not (= x (as sep.nil U))) (sep (not (_ emp U Int)) (pto x 0)))))
; satisfiable with heap of size 2, model of U of size 3
(check-sat)
