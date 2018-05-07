; COMMAND-LINE: --sort-inference --no-check-models
; EXPECT: sat
(set-logic QF_NRA)
(declare-fun x () Real)
(assert (= (* x x) 2.0))
(check-sat)
