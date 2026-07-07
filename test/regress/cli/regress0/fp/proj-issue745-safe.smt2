; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Cannot handle assertion with term of kind"
; EXPECT: Cannot handle assertion with term of kind
; EXIT: 1
(set-option :safe-mode safe)
(set-logic ALL)
(check-sat-assuming ((= RTN RTN)))
