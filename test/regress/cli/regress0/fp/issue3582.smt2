; EXPECT: unsat
(set-logic QF_FP)
(declare-fun bv () (_ BitVec 1))
(define-fun x () (_ FloatingPoint 11 53) ((_ to_fp_unsigned 11 53) RNE bv))
(assert (fp.isNaN x))
(check-sat)
