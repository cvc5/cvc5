; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(set-option :strings-exp true)
(declare-const x Real)
(declare-const _x (Seq RoundingMode))
(check-sat-assuming ((fp.isZero ((_ to_fp 11 53) (seq.nth _x (seq.len _x)) x))))
