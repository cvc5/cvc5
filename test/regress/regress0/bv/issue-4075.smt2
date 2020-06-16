; REQUIRES: no-competition
; EXPECT: (error "Parse Error: issue-4075.smt2:11.26: expecting number of repeats > 0
; EXPECT:
; EXPECT:  (simplify ((_ repeat 0) b))
; EXPECT:                       ^
; EXPECT:")
; EXIT: 1
(set-logic QF_BV)
(define-sort a () (_ BitVec 4))
(declare-const b a)
(simplify ((_ repeat 0) b))
