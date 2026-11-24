; REQUIRES: unrestricted-mode
; COMMAND-LINE: --bv-abstraction --bv-abstraction-size=3
; EXPECT: sat
; A satisfiable n-ary multiplication (a * b * c = 30 with a, b, c > 1).
; BITVECTOR_MULT is n-ary in cvc5, whereas the Table-2 lemma schemes are
; binary, so the term is left-associated into a chain of binary
; multiplications, each abstracted by its own constant. Both chain elements
; have to be refined before the model is consistent with the multiplication.
(set-logic QF_BV)
(set-info :status sat)
(declare-fun a () (_ BitVec 16))
(declare-fun b () (_ BitVec 16))
(declare-fun c () (_ BitVec 16))
(assert (= (bvmul a b c) (_ bv30 16)))
(assert (bvugt a (_ bv1 16)))
(assert (bvugt b (_ bv1 16)))
(assert (bvugt c (_ bv1 16)))
(check-sat)
