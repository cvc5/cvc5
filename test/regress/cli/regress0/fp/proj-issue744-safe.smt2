; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "THEORY_FP is disabled in this configuration, but got a constraint in that theory. Try --fp"
; EXPECT: THEORY_FP is disabled in this configuration, but got a constraint in that theory. Try --fp
; EXIT: 1
(set-option :safe-options true)
(set-logic ALL)
(assert (fp.geq (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)) (fp (_ bv0 1) (_ bv0 11) (_ bv0 52))))
(check-sat)
