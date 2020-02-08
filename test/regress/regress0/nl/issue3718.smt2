; COMMAND-LINE: --quiet
; EXPECT: sat
(set-logic QF_NRAT)
(set-info :status sat)
(assert (= (sqrt 0) 0))
(check-sat)
