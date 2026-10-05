; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(set-option :fp-exp true)
(declare-const x RoundingMode)
(check-sat-assuming ((set.subset (set.singleton (_ bv0 1)) (set.singleton ((_ fp.to_sbv 1) x (_ +zero 15 113))))))
