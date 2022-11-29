; SCRUBBER: grep -o "'re.loop' not declared as a variable"
; EXPECT: 're.loop' not declared as a variable
; EXIT: 1
; DISABLE-TESTER: dump
; REQUIRES: no-competition
(set-logic QF_SLIA)
(assert (re.loop 0))
