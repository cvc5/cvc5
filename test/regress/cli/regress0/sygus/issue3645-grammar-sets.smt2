; EXPECT: sat
; COMMAND-LINE: --sygus-inference=try
(set-logic ALL)
(declare-fun a () (Set (_ BitVec 2)))
(declare-fun b () (Set (_ BitVec 2)))
(assert (= a b))
(check-sat)
