; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "THEORY_FP is disabled in this configuration, but got a constraint in that theory. Try --fp"
; EXPECT: THEORY_FP is disabled in this configuration, but got a constraint in that theory. Try --fp
; EXIT: 1
(set-option :safe-options true)
(set-logic ALL)
(check-sat-assuming ((= RTN RTN)))
