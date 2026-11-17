; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(declare-const __ (_ BitVec 15))
(set-option :fp-exp true)
(set-option :produce-learned-literals true)
(assert (fp.isNaN ((_ to_fp 5 11) ((_ zero_extend 1) __))))
(check-sat)
