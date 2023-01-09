; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "expecting number of repeats > 0"
; EXPECT: expecting number of repeats > 0
; EXIT: 1
(set-logic QF_BV)
(define-sort a () (_ BitVec 4))
(declare-const b a)
(simplify ((_ repeat 0) b))
