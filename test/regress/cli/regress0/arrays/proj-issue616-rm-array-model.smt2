; REQUIRES: unrestricted-mode
; EXPECT: sat
(set-logic ALL)
(set-option :debug-check-models true)
(declare-const x RoundingMode)
(declare-const x4 RoundingMode)
(declare-const x9 (Array RoundingMode RoundingMode))
(check-sat-assuming ((ite (= x9 (store x9 x (select x9 x4))) false true)))
