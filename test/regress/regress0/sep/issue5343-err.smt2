; REQUIRES: no-competition
; COMMAND-LINE:
; EXPECT: (error "ERROR: the type of the separation logic heap has not been declared (e.g. via a declare-heap command), and we have a separation logic constraint (wand true true)
; EXPECT: ")
; EXIT: 1
(set-logic QF_ALL)
(assert (wand true true))
(check-sat)
