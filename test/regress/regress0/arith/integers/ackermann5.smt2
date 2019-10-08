; COMMAND-LINE: --ackermann --no-check-models --no-check-proofs --no-check-unsat-cores
; EXPECT: sat
(set-logic QF_UFLIA)
(set-info :smt-lib-version 2.0)
(set-info :category "crafted")
(declare-fun v0 () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)

(assert (= (f v0) (g (f v0))))
(assert (= (f (f v0)) (g (f v0))))
(assert (= (f (f (f v0))) (g (f v0))))

(check-sat)
(exit)
