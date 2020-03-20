; COMMAND-LINE: --uf-ss-totality --fmf-fun --sort-inference --no-check-models
; EXPECT: sat
(set-logic QF_UFNIA)
(set-info :status sat)
(declare-const i15 Int)
(assert (= true true true (not (= i15 0))))
(check-sat)
(exit)
