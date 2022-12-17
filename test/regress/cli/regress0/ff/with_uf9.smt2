; REQUIRES: cocoa
; EXPECT: unsat
; COMMAND-LINE: --simplification=none
(set-logic QF_FF)
(define-sort FF () (_ FiniteField 17))
(declare-fun a () FF)
(declare-fun b () FF)
(declare-fun c () FF)
(assert (and (= a b) (= b c) (or (not (= a b)) (not (= a c)))))
(check-sat)
