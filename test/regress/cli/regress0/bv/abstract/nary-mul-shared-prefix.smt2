; REQUIRES: unrestricted-mode
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3
; EXPECT: sat
; Two n-ary multiplications sharing a prefix. Since the chain elements are
; cached, the abstraction constant introduced for (bvmul a b) is shared by both
; chains, i.e. three abstraction constants are introduced rather than four.
; Refining the shared element constrains both products at once.
(set-logic QF_BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
(declare-fun d () (_ BitVec 16))
(assert (bvult (bvmul a b c) (bvmul a b d)))
(assert (bvugt a (_ bv1 16)))
(assert (bvugt b (_ bv1 16)))
(check-sat)
