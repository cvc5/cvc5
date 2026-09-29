; REQUIRES: unrestricted-mode
; SCRUBBER: grep -v fp.to_sbv
; EXPECT: sat
(set-logic ALL)
(set-option :produce-models true)
(declare-const x RoundingMode)
(check-sat)
(get-value (((_ fp.to_sbv 24) x ((_ to_fp 11 53) x #b1000000000000000000000000000000000000000))))
