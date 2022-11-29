; COMMAND-LINE: --nl-rlv=always
; EXPECT: sat
(set-logic QF_NRAT)
(set-info :status sat)
(declare-fun x () Real)
(assert (or (= x (sin 0.1)) (= x (sin 1.1))))
(check-sat)
