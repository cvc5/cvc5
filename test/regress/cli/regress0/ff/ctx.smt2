; REQUIRES: cocoa
; EXPECT: sat
; EXPECT: unsat
; EXPECT: sat
; EXPECT: sat
; COMMAND-LINE: --incremental
; Tests the ff rewriter
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
; all disjuncts should be false
(define-sort F () (_ FiniteField 17))
(declare-fun a () F)
(declare-fun b () F)
(assert (= (ff.mul a a) b))
(assert (= a (as ff1 F)))
(check-sat)
(push)
(declare-fun c () F)
(assert (= (ff.mul c c) c))
(assert (= (ff.mul c c) (ff.mul (as ff2 F) b)))
(check-sat)
(pop)
(push)
(declare-fun c () F)
(assert (= (ff.mul c c) c))
(assert (= (ff.mul c c) b))
(check-sat)
(check-sat)
(pop)
