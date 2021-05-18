; COMMAND-LINE: --ackermann
; EXPECT: sat
(set-logic QF_UFLIA)
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(declare-fun v0 () Int)
(declare-fun f (Int) Int)
(declare-fun g (Int) Int)

(assert (= (f v0) (g (f v0))))
(assert (= (f (f v0)) (g (f v0))))
(assert (= (f (f (f v0))) (g (f v0))))

(check-sat)
(exit)
