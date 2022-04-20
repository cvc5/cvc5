; COMMAND-LINE: -q --sygus-inst
; EXPECT: sat
(set-logic ALL)
(declare-fun a (Bool) Bool)
(assert (forall ((b Bool)) (= (a b) (not b))))
(check-sat)
