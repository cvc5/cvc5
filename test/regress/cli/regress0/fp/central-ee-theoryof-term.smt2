; REQUIRES: unrestricted-mode
; COMMAND-LINE: --ee-mode=central --theoryof-mode=term
; EXPECT: unsat
; With --theoryof-mode=term, (= x one) is owned by THEORY_UF (x is a
; variable). With --ee-mode=central, THEORY_FP never received it as a fact,
; thus the word-blasting did not know that x is not one.
(set-logic QF_UFFP)
(declare-fun x () Float32)
(define-fun one () Float32 ((_ to_fp 8 24) RNE 1.0))
(assert (not (= x one)))
(assert (= (fp.mul RNE x one) one))
(check-sat)
