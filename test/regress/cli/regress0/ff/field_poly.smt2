; REQUIRES: cocoa
; EXPECT: unsat
; COMMAND-LINE: --ff-field-polys
; COMMAND-LINE:
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
; all disjuncts should be false
(define-sort F3 () (_ FiniteField 3))
(declare-fun a () F3)
(assert (= (ff.mul
    (ff.add a (ff.neg (as ff0 F3)))
    (ff.add a (ff.neg (as ff1 F3)))
    (ff.add a (ff.neg (as ff2 F3)))
    ) (as ff1 F3)))
(check-sat)

