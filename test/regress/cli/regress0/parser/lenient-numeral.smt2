; COMMAND-LINE: --parsing-mode=lenient
; EXPECT: unsat
(set-logic QF_LIRA)
(declare-fun @x () Int)
(declare-fun .y () Int)
(assert (= @x 3))
(assert (= @x -2))
(assert (distinct @x .y))
(check-sat)
