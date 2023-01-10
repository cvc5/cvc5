; REQUIRES: cocoa
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_UFFF)
(define-sort FF () (_ FiniteField 17))
(declare-fun f (FF) FF)
(declare-fun a () FF)
(declare-fun b () FF)
(declare-fun c () FF)
(declare-fun e1 () Bool)
(declare-fun e2 () Bool)
(declare-fun e3 () Bool)
(assert (not (= (f a) (f c))))

; b = c
(assert (= (ff.mul c c) c))
(assert (= (ff.mul b b) b))
(assert (or (= (ff.add (as ff1 FF) (ff.neg c) (ff.neg b) (ff.mul (as ff2 FF) c b)) (as ff1 FF)) (and e1 e2 e3)))

; a = b
(assert (= (ff.mul a a) a))
(assert (= (ff.mul b b) b))
(assert (= (ff.add (as ff1 FF) (ff.neg a) (ff.neg b) (ff.mul (as ff2 FF) a b)) (as ff1 FF)))
(check-sat)

