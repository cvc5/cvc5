; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic QF_ALL)
(declare-const __ (_ BitVec 1))
(set-option :fp-exp true)
(declare-const x RoundingMode)
(assert (fp.leq ((_ to_fp 5 11) x ((_ zero_extend 10) __)) (fp (_ bv0 1) (_ bv0 5) (_ bv0 10))))
(check-sat)
