; REQUIRES: portfolio
; COMMAND-LINE: --use-portfolio --portfolio-dry-run
; SCRUBBER: grep -o -- "--sat-solver=cadical" | head -n 1
; EXPECT: --sat-solver=cadical
; EXIT: 0
; DISABLE-TESTER: dump
(set-logic QF_LIA)
(check-sat)
