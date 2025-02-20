; COMMAND-LINE: --sygus-inst
; EXPECT: unsat
(set-logic ALL)
(declare-fun r () (Array Int (Array Int Int)))
(assert (forall ((a (Array Int (Array Int Int)))) (= r a)))
(check-sat)
