; COMMAND-LINE: -i
; EXPECT: sat
(set-logic QF_ALIA)
(set-info :status sat)
(declare-fun i2 () Int)
(declare-fun arr0 () (Array Int Bool))
(declare-fun i10 () Int)
(assert (select (store (store arr0 1 true) i10 false) i2))
(push)
(assert (= i10 0))
(check-sat)
