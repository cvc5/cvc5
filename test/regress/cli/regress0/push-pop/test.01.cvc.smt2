; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-fun x () Bool)
(declare-fun y () Bool)
(assert (or x y))
(check-sat)
(push 1)
(assert (not x))
(check-sat)
(pop 1)
(push 1)
(assert (not y))
(check-sat)
(pop 1)
(check-sat)
