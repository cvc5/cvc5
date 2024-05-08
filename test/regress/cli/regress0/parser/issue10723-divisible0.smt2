; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Invalid value '0' at index 0 for operator"
; EXPECT: Invalid value '0' at index 0 for operator
; EXIT: 1
(set-logic ALL)
(assert (forall ((v Real)) ((_ divisible 0) v)))
(check-sat)
