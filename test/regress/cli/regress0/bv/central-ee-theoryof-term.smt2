; REQUIRES: unrestricted-mode
; COMMAND-LINE: --ee-mode=central --theoryof-mode=term
; COMMAND-LINE: --ee-mode=central --theoryof-mode=term --bv-solver=bitblast-internal
; EXPECT: unsat
; With --theoryof-mode=term, (= x #b00) is owned by THEORY_UF (x is a
; variable). With --ee-mode=central, THEORY_BV never received it as a fact,
; thus the bit-blaster did not know that x is not zero.
(set-logic QF_UFBV)
(declare-fun x () (_ BitVec 2))
(assert (not (= x #b00)))
(assert (not (= (bvudiv x x) #b01)))
(check-sat)
