; COMMAND-LINE: -i
; EXPECT: unsat
; EXPECT: unsat
(set-logic QF_NRAT)
(declare-const r0 Real)
(assert (! (>= (sin 97111.0) r0 r0 r0 97111.0) :named IP_3))
(push 1)
(check-sat)
(pop 1)
(check-sat)
