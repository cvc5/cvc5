; COMMAND-LINE: --solve-int-as-bv=64 --ackermann
; DISABLE-TESTER: model
; EXPECT: sat
(set-logic QF_UFLIA)
(declare-fun f (Int) Int)
(declare-const x Int)
(declare-const y Int)
(assert (= (f x) (f y)))
(assert (>= x 0))
(assert (>= y 0))
(check-sat)
