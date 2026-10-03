; REQUIRES: unrestricted-mode
; EXPECT: sat
; EXPECT: (((pto x y) true))
; EXPECT: (((pto (+ x 1) y) false))
; EXPECT: ((sep.emp false))
; get-value on separation logic atoms returns concrete Boolean values,
; evaluated against the model heap (they are Boolean-sorted terms).
(set-logic QF_ALL)
(set-option :produce-models true)
(declare-heap (Int Int))
(declare-const x Int)
(declare-const y Int)
(assert (pto x y))
(check-sat)
(get-value ((pto x y)))
(get-value ((pto (+ x 1) y)))
(get-value (sep.emp))
