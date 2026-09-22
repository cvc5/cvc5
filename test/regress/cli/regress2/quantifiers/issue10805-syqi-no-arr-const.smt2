; COMMAND-LINE: --sygus-inst
; EXPECT: unsat
; DISABLE-TESTER: lfsc
; DISABLE-TESTER: proof
(set-logic ALL)
(declare-const x (Array Bool (Array Bool Bool)))
(assert (forall ((v (Array Bool (Array Bool Bool)))) (set.subset (set.singleton v) (set.singleton x))))
(check-sat)
