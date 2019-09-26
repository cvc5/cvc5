; COMMAND-LINE: --ackermann
; EXPECT: sat
(set-logic QF_UFLIA)
(declare-fun a () Int)
(declare-fun b () Int)
(declare-fun f (Int) Int)
(assert (= (f a) (f b)))
(check-sat)
(exit)
