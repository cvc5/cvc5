; COMMAND-LINE: --produce-models --model-cores=simple
; COMMAND-LINE: --produce-models --model-core=non-implied
; EXPECT: sat
(set-logic QF_UFLIA)
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(declare-fun f (Int) Int)
(assert (= (f x) 0))
(assert (or (> z 5) (> y 5)))
(check-sat)
