; REQUIRES: poly
; SCRUBBER: grep -o "Term of kind sin is not compatible"
; EXPECT: Term of kind sin is not compatible
; EXIT: 1
(set-logic NRAT)
(set-option :nl-cov true)
(assert (exists ((r Real)) (distinct 0.0 (sin 1.0))))
(check-sat)
