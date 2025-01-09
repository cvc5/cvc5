; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "All formal arguments to defined functions must be unique"
; EXPECT: All formal arguments to defined functions must be unique
; EXIT: 1
(set-logic ALL)
(define-fun P ((x Int) (x Int)) Bool (= x 0))
(assert (P 0 1))
(check-sat)
