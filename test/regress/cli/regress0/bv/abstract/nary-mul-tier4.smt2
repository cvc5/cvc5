; REQUIRES: unrestricted-mode
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3 --bv-abstraction-value-limiter=100
; EXPECT: sat
; Forces the tier-4 bit-blasting fallback on a binarized chain: the tier-3
; value-instantiation budget is bit-width/100 = 0, so any chain element that
; no Table-2 lemma rules out falls back to asserting the real multiplication
; right away. Note that tier 4 on a chain element asserts t2 = bvmul(t1, c)
; against the still-abstract t1, i.e. it bit-blasts a single multiplier: the
; whole product only becomes exact once every element has fallen back.
(set-logic QF_BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
(declare-fun d () (_ BitVec 16))
(assert (= (bvmul a b c d) (_ bv210 16)))
(assert (bvugt a (_ bv1 16)))
(assert (bvugt b (_ bv1 16)))
(assert (bvugt c (_ bv1 16)))
(assert (bvugt d (_ bv1 16)))
(check-sat)
