; COMMAND-LINE: --decision=internal
; EXPECT: sat
(set-logic ALL)
(declare-fun r () Real)
(declare-fun a () (Array Real Bool))
(assert (or (select a 0.0) (select a 1.0) (= r 0.0) (select a (* r r 1.0))))
(check-sat)
