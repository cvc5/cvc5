; REQUIRES: no-competition
; SCRUBBER: grep -o "Cannot name a term in a binder"
; EXPECT: Cannot name a term in a binder
; EXIT: 1
(set-logic QF_UF)
(define-fun f () Bool (! false :named foo))
