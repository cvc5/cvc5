; REQUIRES: unrestricted-mode
; COMMAND-LINE: -q
; EXPECT: sat
(set-logic ALL)
(set-option :deep-restart all)
(declare-const x Real)
(assert (< (sin x) (arcsec x)))
(check-sat)
