; COMMAND-LINE: --ackermann --no-check-models  --no-check-unsat-cores
; EXPECT: unsat
(set-logic QF_UFLIA)

(declare-fun a () Int)
(declare-fun b () Int)

(declare-fun f (Int) Int)
(declare-fun g (Int) Int)

(assert (= (f (g (f (f a)))) (f (g (f a)))))
(assert (= (f a) b))
(assert (= (f b) a))
(assert (not (= a b)))
(assert (= (g a) (f a)))
(assert (= (g b) (f b)))

(check-sat)
(exit)