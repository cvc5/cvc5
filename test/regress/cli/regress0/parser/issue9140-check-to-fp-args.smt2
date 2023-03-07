; DISABLE-TESTER: dump
; SCRUBBER: grep -o "expected a value > 1"
; EXPECT: expected a value > 1
; EXIT: 1
(set-logic ALL)
(assert (forall ((a Real)) (= ((_ to_fp 0 1) 0.0))))
