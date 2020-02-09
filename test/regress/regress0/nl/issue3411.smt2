; COMMAND-LINE: --no-check-models
; EXPECT: sat
(set-logic NRA)
(set-info :status sat)
(declare-fun a () Real)
(declare-fun b () Real)
(assert (= (/ 0 (+ 1 (* a a b))) 0))
(check-sat)
