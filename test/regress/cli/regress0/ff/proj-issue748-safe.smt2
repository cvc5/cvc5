; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "THEORY_FF is disabled in this configuration, but got a constraint in that theory. Try --ff"
; EXPECT: THEORY_FF is disabled in this configuration, but got a constraint in that theory. Try --ff
; EXIT: 1
(set-option :safe-options true)
(set-logic ALL)
(set-option :produce-learned-literals true)
(assert (= #f0m29 (ff.mul #f0m29 #f0m29)))
(check-sat)
