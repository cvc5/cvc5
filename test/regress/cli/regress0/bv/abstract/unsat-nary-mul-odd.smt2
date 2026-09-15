; REQUIRES: unrestricted-mode
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3
; EXPECT: unsat
; DISABLE-TESTER: proof
; If a, b and c are odd then a * b * c is odd. The multiplication is written
; in explicitly nested binary form: the rewriter flattens nested bvmul into a
; single n-ary node, so this is the very same term as (bvmul a b c) by the
; time the abstraction sees it -- an n-ary multiplication cannot be avoided by
; writing it as a chain. Refuting this only needs the MUL4_ODD scheme
; instantiated for each element of the binarized chain, no tier-3/4 fallback.
(set-logic QF_BV)
(set-info :status unsat)
(declare-fun a () (_ BitVec 32))
(declare-fun b () (_ BitVec 32))
(declare-fun c () (_ BitVec 32))
(assert (= ((_ extract 0 0) a) #b1))
(assert (= ((_ extract 0 0) b) #b1))
(assert (= ((_ extract 0 0) c) #b1))
(assert (= ((_ extract 0 0) (bvmul (bvmul a b) c)) #b0))
(check-sat)
