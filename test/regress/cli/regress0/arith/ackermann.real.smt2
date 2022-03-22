; COMMAND-LINE: --ackermann 
; EXPECT: unsat
(set-logic QF_UFNRA)

(declare-fun a () Real)
(declare-fun b () Real)

(declare-fun f (Real) Real)
(declare-fun g (Real) Real)

(assert (= (f (g (f (f a)))) (f (g (f a)))))
(assert (= (f a) b))
(assert (= (f b) a))
(assert (not (= a b)))
(assert (= (g a) (f a)))
(assert (= (g b) (f b)))

(check-sat)
(exit)