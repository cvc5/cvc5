; REQUIRES: no-competition
; EXPECT-ERROR: (error "ERROR: the type of the separation logic heap has not been declared (e.g. via a declare-heap command), and we have a separation logic constraint (wand true true)
; EXPECT-ERROR: ")
; EXIT: 1
(set-logic QF_ALL_SUPPORTED)
(assert (wand true true))
(check-sat)
