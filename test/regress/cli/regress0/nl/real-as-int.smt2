; COMMAND-LINE: --solve-real-as-int 
; EXPECT: sat
(set-logic QF_NRA)
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= (* a a) 4.0))
(assert (= (* b b) 0.0))
(assert (= (+ (* a a) (* b b)) 4.0))
(check-sat)
