; EXPECT: sat
; COMMAND-LINE: --sygus-inference=try --arrays-exp
(set-logic ALL)
(declare-fun a () (Array Int Int))
(declare-fun b () (Array Int Int))
(assert (= a b))
(check-sat)
