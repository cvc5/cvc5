; REQUIRES: cocoa
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_UFFF)
(define-sort FF () (_ FiniteField 17))
(declare-fun g (FF) FF)
(declare-fun f (FF) FF)
(declare-fun a () FF)
(declare-fun b () FF)
(declare-fun c () FF)
(declare-fun d () FF)
(declare-fun e () FF)
(assert (= a (g c)))
(assert (= b (g d)))

; c = d
(assert (= (ff.mul c c) c))
(assert (= (ff.mul d d) d))
(assert (= (ff.add (as ff1 FF) (ff.neg c) (ff.neg d) (ff.mul (as ff2 FF) c d)) (as ff1 FF)))

; b = e
(assert (= (ff.mul b b) b))
(assert (= (ff.mul e e) e))
(assert (= (ff.add (as ff1 FF) (ff.neg b) (ff.neg e) (ff.mul (as ff2 FF) b e)) (as ff1 FF)))

(assert (not (= (f a) (f e))))

(check-sat)

