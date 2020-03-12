; COMMAND-LINE: --solve-real-as-int
; EXPECT: sat
(set-logic QF_UFNIRA)
(set-info :status sat)
(declare-fun f (Real) Int)
(declare-fun a () Real)
(assert (= (f a) 0))
(check-sat)
