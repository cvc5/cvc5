; REQUIRES: cocoa
; EXPECT: sat
; COMMAND-LINE: --ff-solver split
; COMMAND-LINE: --ff-solver gb
(set-info :smt-lib-version 2.6)
(set-info :category "crafted")
(set-logic QF_FF)
(define-sort FF () (_ FiniteField 21888242871839275222246405745257275088548364400416034343698204186575808495617))
(declare-const _0 FF)
(declare-const _1 FF)
(assert (= (ff.add (ff.mul (as ff-2 FF) _0) (ff.mul (as ff-1 FF) _1) (as ff4 FF)) (as ff0 FF)))
(check-sat)
