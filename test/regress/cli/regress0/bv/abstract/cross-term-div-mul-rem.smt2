; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3
; EXPECT: unsat
; DISABLE-TESTER: proof
; The division identity a = (a udiv b) * b + (a urem b) for b != 0. The
; inconsistency stems from the interaction of three abstracted terms (bvudiv,
; bvmul, bvurem), so no single-operator Table-2 lemma rules it out: this
; exercises the tier-3 value-instantiation / tier-4 bit-blasting fallback.
(set-logic QF_BV)
(set-info :status unsat)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(assert (distinct (bvadd (bvmul (bvudiv a b) b) (bvurem a b)) a))
(assert (distinct b (_ bv0 4)))
(check-sat)
