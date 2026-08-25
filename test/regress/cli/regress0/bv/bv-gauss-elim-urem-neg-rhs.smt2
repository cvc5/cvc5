; COMMAND-LINE: --bv-gauss-elim
; EXPECT: sat
; Regression for a bug where Gaussian elimination over UREM equations produced
; spurious UNSAT: a negative right-hand side (after subtracting BVADD constants
; larger than the UREM rhs) was reduced modulo 2^width by the BitVector
; constructor instead of modulo the UREM divisor.
(set-logic QF_BV)
(declare-fun a () (_ BitVec 4))
(declare-fun b () (_ BitVec 4))
(assert (= (bvurem (bvadd ((_ zero_extend 4) a) (_ bv7 8)) (_ bv5 8)) (_ bv2 8)))
(assert (= (bvurem (bvadd ((_ zero_extend 4) b) (_ bv6 8)) (_ bv5 8)) (_ bv1 8)))
(check-sat)
