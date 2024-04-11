; COMMAND-LINE: -o options-auto
; SCRUBBER: sed -e 's/(options-auto.*//'
; EXPECT: unsat
(set-logic QF_LRA)
(assert false)
(check-sat)
