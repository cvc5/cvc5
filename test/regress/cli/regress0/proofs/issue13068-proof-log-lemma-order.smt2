; REQUIRES: unrestricted-mode
; COMMAND-LINE: --proof-log
; DISABLE-TESTER: alethe
; DISABLE-TESTER: cpc
; SCRUBBER: grep -E '^(sat|unsat)$'
; EXPECT: unsat
(set-logic QF_LIRA)
(declare-fun r () Real)
(assert (> (to_int r) r))
(check-sat)
