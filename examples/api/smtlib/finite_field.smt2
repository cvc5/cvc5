(set-logic QF_FF)
(set-option :incremental true)

(define-sort F () (_ FiniteField 5))

(declare-fun a () F)
(declare-fun b () F)

; ab = 1
(assert (= (ff.mul a b) (as ff1 F)))

; a = 2
(assert (= a (as ff2 F)))

; SAT
(check-sat)

; b = 2
(assert (= b (as ff2 F)))

; UNSAT
(check-sat)

