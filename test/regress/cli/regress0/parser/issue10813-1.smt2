; DISABLE-TESTER: dump
; SCRUBBER: grep -o 'cannot construct Real or Int from string argument'
; EXPECT: cannot construct Real or Int from string argument
; EXIT: 1
(set-logic QF_LRA)
(declare-const x Real)
(declare-const y Real)
(assert (> x 1.5))
(assert (< y 3.5))
(assert (= (+ x y) 5/0))
(check-sat)
