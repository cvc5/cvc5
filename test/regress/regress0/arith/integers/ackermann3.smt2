; COMMAND-LINE: --ackermann 
; EXPECT: sat
(set-logic QF_UFLIA)

(declare-fun a () Int)
(declare-fun b () Int)

(declare-fun f (Int) Int)
(declare-fun g (Int) Int)

(assert (= (f (g (f (f a)))) (f (g (f (f b))))))
(assert (not (= a b)))

(check-sat)
(exit)
