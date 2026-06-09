; COMMAND-LINE: --ee-mode=central
; EXPECT: unsat
(set-logic QF_AUFLIA)
(declare-fun a () (Array Int Int))
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun g ((Array Int Int)) Int)
(declare-fun f (Int) Int)
(assert (and (distinct (f x) (f y)) (= (store a y 0) (store a x 0)) (distinct (g a) (g (store a y 0)))))
(check-sat)
