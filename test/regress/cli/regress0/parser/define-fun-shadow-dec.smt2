; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "All formal arguments to defined functions must be unique"
; EXPECT: All formal arguments to defined functions must be unique
; EXIT: 1
(set-logic QF_BV)
(declare-const x Bool)
(define-fun P ((x Bool) (x Bool)) Bool x)
(assert (P false true))
(check-sat)
