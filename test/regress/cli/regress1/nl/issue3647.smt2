; COMMAND-LINE: --produce-models --decision=internal --nl-rlv=always -q
; EXPECT: sat
(set-logic QF_NRAT)
(set-info :status sat)
(assert (distinct (sin 1.0) 0.0))
(check-sat)
