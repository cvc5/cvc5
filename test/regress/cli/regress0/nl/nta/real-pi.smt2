; COMMAND-LINE: --nl-ext=full -q
; EXPECT: sat
(set-logic QF_NRAT)
(set-info :status sat)
(assert (<= 3.0 real.pi))
(assert (<= real.pi 4.0))
(check-sat)
