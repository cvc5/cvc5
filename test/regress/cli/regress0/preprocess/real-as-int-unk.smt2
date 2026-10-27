; COMMAND-LINE: --solve-real-as-int
; EXPECT: unknown
(set-logic ALL)
(declare-fun x () Real)
(assert (< 0.0 x 1.0))
(check-sat)
