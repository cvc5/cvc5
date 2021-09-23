; COMMAND-LINE: --fmf-fun --sort-inference
; EXPECT: sat
(set-logic QF_UFNIA)
(set-info :status sat)
(declare-const i15 Int)
(assert (= true true true (not (= i15 0))))
(check-sat)
(exit)
