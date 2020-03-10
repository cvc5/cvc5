; COMMAND-LINE: --incremental --solve-real-as-int
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-logic ALL)
(declare-fun x () Real)
(declare-fun y () Real)

(assert (> x y))
(assert (> x 500.5))

(check-sat)

(push 1)
(declare-fun z () Real)
(assert (> z x))
(check-sat)
(pop 1)

(push 1)
(declare-fun w () Real)
(assert (> w x))
(check-sat)
(pop 1)
