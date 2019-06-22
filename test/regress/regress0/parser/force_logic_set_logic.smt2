; This regression ensures that we detect repeated set-logic commands even when
; --force-logic is used.

; COMMAND-LINE: --force-logic="QF_BV"
; SCRUBBER: grep -o "Only one set-logic is allowed."
; EXPECT: Only one set-logic is allowed.
; EXIT: 1
(set-logic QF_BV)
(set-logic QF_BV)
