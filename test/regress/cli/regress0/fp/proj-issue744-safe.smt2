; DISABLE-TESTER: dump
; REQUIRES: no-competition
; SCRUBBER: grep -o "Cannot handle assertion with term of kind"
; EXPECT: Cannot handle assertion with term of kind
; EXIT: 1
(set-option :safe-mode safe)
(set-logic ALL)
(assert (fp.geq (fp (_ bv0 1) (_ bv0 11) (_ bv0 52)) (fp (_ bv0 1) (_ bv0 11) (_ bv0 52))))
(check-sat)
