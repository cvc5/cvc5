; REQUIRES: cocoa
; EXPECT: sat
; Tests the ff rewriter
; COMMAND-LINE: --decision=justification
; COMMAND-LINE: --ff-field-polys
; COMMAND-LINE:
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
; all disjuncts should be false
(define-sort F3 () (_ FiniteField 3))
(define-sort F5 () (_ FiniteField 5))
(declare-fun a () F3)
(declare-fun b () F5)
(assert (or (= (ff.mul
    (ff.add a (ff.neg (as ff0 F3)))
    (ff.add a (ff.neg (as ff1 F3)))
    (ff.add a (ff.neg (as ff2 F3)))
    ) (as ff1 F3))
(= (ff.mul
    (ff.add b (ff.neg (as ff0 F5)))
    (ff.add b (ff.neg (as ff1 F5)))
    (ff.add b (ff.neg (as ff2 F5)))
    ) (as ff1 F5))))
(check-sat)
