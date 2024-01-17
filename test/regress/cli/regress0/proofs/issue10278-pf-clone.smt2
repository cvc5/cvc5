; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "unsat"
; EXPECT: unsat
; EXIT: 1
(set-logic ALL)
(declare-const x Int)
(declare-const y Int)
(assert (<= 0 x))
(assert (<= 0 y))
(assert (< x 2))
(assert (< y 2))
(assert (not (< (* x y) 2)))
(check-sat)
(get-proof)
(get-proof)
