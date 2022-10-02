; COMMAND-LINE: --decision=internal
; COMMAND-LINE: --decision=justification
; EXPECT: sat
(set-info :smt-lib-version 2.6)
(set-logic QF_BVFP)
(declare-fun a () (_ BitVec 64))
(declare-fun b () (_ BitVec 64))
(assert (fp.leq ((_ to_fp 11 53) a) ((_ to_fp 11 53) (_ bv4626322717216342016 64))))
(assert (not (fp.isNaN ((_ to_fp 11 53) b))))
(declare-fun k2 () (_ BitVec 64))
(assert (or (= k2 b) (= k2 a)))
(assert
(or (fp.isNaN ((_ to_fp 11 53) k2)) (fp.gt ((_ to_fp 11 53) k2) ((_ to_fp 11 53) (_ bv4626322717216342016 64))) ))
(check-sat)
