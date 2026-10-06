; REQUIRES: unrestricted-mode
; SCRUBBER: grep -v -E '\(|\)'
; EXPECT: unsat
; DISABLE-TESTER: proof
(set-logic ALL)
(set-option :dump-difficulty true)
(set-option :proof-elim-subtypes true)
(assert (= real.pi (arcsec real.pi)))
(check-sat)
