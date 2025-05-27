; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Cannot handle assertion with term of kind"
; EXPECT: Cannot handle assertion with term of kind
; EXIT: 1
(set-option :safe-mode safe)
(set-logic ALL)
(set-option :produce-learned-literals true)
(assert (= #f0m29 (ff.mul #f0m29 #f0m29)))
(check-sat)
