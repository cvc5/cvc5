;COMMAND-LINE: --check-models
;EXIT: 1
;EXPECT: (error "Cannot run check-model on a model with approximate values.")
(set-logic QF_NRA)
(declare-fun a () Real)
(assert (= (* a a) 2))
(check-sat)
