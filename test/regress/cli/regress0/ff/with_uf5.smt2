; REQUIRES: cocoa
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_UFFF)
(define-sort FF () (_ FiniteField 17))
(declare-fun g (FF) FF)
(declare-fun a () FF)
(declare-fun b () FF)
(declare-fun c () FF)
(declare-fun d () FF)
(assert (= a (g c)))
(assert (= b (g d)))

; c = d
(assert (= (ff.mul c c) c))
(assert (= (ff.mul d d) d))
(assert (= (ff.add (as ff1 FF) (ff.neg c) (ff.neg d) (ff.mul (as ff2 FF) c d)) (as ff1 FF)))

(assert (= a (ff.add b (as ff1 FF))))

(check-sat)

