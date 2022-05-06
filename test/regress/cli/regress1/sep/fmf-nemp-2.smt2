; COMMAND-LINE: --finite-model-find
; EXPECT: sat
; DISABLE-TESTER: model
(set-logic ALL)
(declare-sort U 0)
(declare-heap (U Int))
(declare-fun u1 () U)
(declare-fun u2 () U)
(assert (not (= u1 u2)))
(assert (forall ((x U)) (=> (not (= x (as sep.nil U))) (sep (not sep.emp) (pto x 0)))))
; satisfiable with heap of size 2, model of U of size 3
(check-sat)
