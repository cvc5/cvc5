; COMMAND-LINE: --strict-parsing
; EXPECT: sat
(set-logic QF_LIRA)
(declare-fun x () Int)
(declare-fun -2 () Int)
(assert (= x 3))
(assert (= x -2))
(check-sat)
