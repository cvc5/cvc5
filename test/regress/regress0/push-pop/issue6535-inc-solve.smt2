; COMMAND-LINE: -i
; EXPECT: sat
(set-logic ALL)
(declare-fun f0_2 (Real Real) Real)
(declare-fun x8 () Real)
(assert (= 0.0 (f0_2 x8 1.0)))
(push)
(assert (= x8 1.0))
(check-sat)
