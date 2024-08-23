; COMMAND-LINE: -o options-auto
; SCRUBBER: sed -e 's/(options-auto.*//'
; EXPECT: sat
(set-logic QF_LRA)
(assert true)
(check-sat)
