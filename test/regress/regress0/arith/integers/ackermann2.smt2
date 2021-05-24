; COMMAND-LINE: --ackermann 
; EXPECT: unsat
(set-logic QF_UFLIA)

(declare-fun a () Int)
(declare-fun b () Int)

(declare-fun f (Int) Int)
(declare-fun g (Int) Int)

(assert (not (= (f (g (f (f a)))) (f (g (f (f b)))))))
(assert (= a b))

(check-sat)
(exit)
