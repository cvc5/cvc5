; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-fun x () Bool)
(push 1)
(assert x)
(check-sat)
(pop 1)
(assert (not x))
(check-sat)
