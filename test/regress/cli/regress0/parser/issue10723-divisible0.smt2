; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "invalid value '0' at index 0 for operator"
; EXPECT: invalid value '0' at index 0 for operator
; EXIT: 1
(set-logic ALL)
(assert (forall ((v Real)) ((_ divisible 0) v)))
(check-sat)
