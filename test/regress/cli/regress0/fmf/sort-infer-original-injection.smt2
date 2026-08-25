; COMMAND-LINE: --finite-model-find --sort-inference
; EXPECT: unsat
; DISABLE-TESTER: lfsc
(set-logic UFC)
(declare-sort U 0)
(declare-const a U)
(declare-const b U)
(declare-const q Bool)
(assert (= (ite q a b) a))
(assert (not (_ fmf.card U 1)))
(assert (forall ((x U) (y U)) (= x y)))
(check-sat)
