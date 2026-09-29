; REQUIRES: unrestricted-mode
; SCRUBBER: grep -v -E '\(|\)'
; EXPECT: unsat
(set-logic ALL)
(set-option :proof-elim-subtypes true)
(assert (= real.pi (arcsec real.pi)))
(check-sat)
