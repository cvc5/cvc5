; REQUIRES: portfolio
; COMMAND-LINE: --use-portfolio --portfolio-dry-run
; SCRUBBER: sed -n '/--sat-solver=cadical/p'
; EXIT: 0
; DISABLE-TESTER: dump
(set-logic QF_SLIA)
(check-sat)
