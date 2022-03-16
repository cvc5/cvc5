; EXPECT: sat
; COMMAND-LINE: --sygus-inference
(set-logic ALL)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (= a b))
(check-sat)
