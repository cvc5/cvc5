; COMMAND-LINE: -q
; EXPECT: sat
(set-logic QF_NRAT)
(set-info :status sat)

(assert (and (<= 3.0 (exp 1.1)) (<= (exp 1.1) 3.1)))
(assert (and (<= 8.1 (exp 2.1)) (<= (exp 2.1) 8.2)))
(assert (and (<= 22.1 (exp 3.1)) (<= (exp 3.1) 22.2)))
(assert (and (<= 60.3 (exp 4.1)) (<= (exp 4.1) 60.4)))
(assert (and (<= 164.0 (exp 5.1)) (<= (exp 5.1) 164.1)))

; this takes ~10 seconds in production
;(assert (and (<= 536190464.4 (exp 20.1)) (<= (exp 20.1) 536190464.5)))

(check-sat)
