; COMMAND-LINE: -i
; EXPECT: sat
; EXPECT: sat
(set-logic QF_ALIA)
(declare-fun v0 () Bool)
(declare-fun i1 () Int)
(declare-fun arr0 () (Array Int Bool))
(assert (select (store arr0 0 v0) i1))
(push)
(assert (= 1 i1))
(check-sat)
(check-sat)
