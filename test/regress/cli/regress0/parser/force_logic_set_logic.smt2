; Note that we do not detect repeated set-logic commands when
; --force-logic is used.

; COMMAND-LINE: --force-logic="QF_BV"
; EXIT: 0
(set-logic QF_BV)
(set-logic QF_BV)
