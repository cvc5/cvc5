; COMMAND-LINE: --finite-model-find
; EXPECT: unsat
(set-logic ALL)
(set-info :status unsat)
(declare-fun f (Bool) Bool)
(assert (forall ((x Bool)) (f (not x))))
(assert (=> (f true) false))
(check-sat)
