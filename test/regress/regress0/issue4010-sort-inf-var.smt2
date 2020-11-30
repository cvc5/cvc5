; COMMAND-LINE: --sort-inference --no-check-models
; EXPECT: sat
(set-logic ALL)
(set-info :status sat)
(declare-fun a () Bool)
(assert a)
(check-sat)
