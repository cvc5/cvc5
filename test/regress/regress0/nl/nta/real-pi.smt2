; COMMAND-LINE: --nl-ext --no-check-models
; EXPECT: sat
(set-logic QF_NRAT)
(set-info :status sat)
(assert (<= 3.0 real.pi))
(assert (<= real.pi 4.0))
(check-sat)
