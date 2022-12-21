; REQUIRES: cocoa
; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_UFFF)
(define-sort FF () (_ FiniteField 17))
(declare-fun f (FF) FF)
(declare-fun a () FF)
(declare-fun b () FF)
(declare-fun c () FF)
(declare-fun e () FF)
(assert (not (= (f a) (f c))))
(assert (= b c))
(assert (= (ff.mul a a) a))
(assert (= (ff.mul b b) b))
(assert (= (ff.add (as ff1 FF) (ff.neg a) (ff.neg b) (ff.mul (as ff2 FF) a b)) (as ff1 FF)))
(check-sat)

