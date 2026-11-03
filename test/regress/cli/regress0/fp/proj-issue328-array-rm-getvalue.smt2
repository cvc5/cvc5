; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(set-option :fp-exp true)
(declare-const x RoundingMode)
(declare-const _x (Array Float16 RoundingMode))
(declare-const x8 (_ BitVec 1))
(check-sat-assuming ((= _x (store _x (fp x8 (_ bv0 5) (_ bv0 10)) x))))
