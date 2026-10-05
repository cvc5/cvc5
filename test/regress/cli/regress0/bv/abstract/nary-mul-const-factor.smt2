; REQUIRES: unrestricted-mode
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3
; EXPECT: sat
; An n-ary multiplication with a (non-power-of-two) constant factor. The
; rewriter folds all constant factors into a single one and sorts it last, so
; left-associating the chain leaves the constant multiplication as the
; outermost element, which is what the coefficient-extraction invariant of the
; BV normalization rewrites expects ("only one constant, at the end").
(set-logic QF_BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(assert (= (bvmul a b (_ bv3 16)) (_ bv30 16)))
(assert (bvugt a (_ bv1 16)))
(assert (bvugt b (_ bv1 16)))
(check-sat)
