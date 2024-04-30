; EXPECT: unsat
(set-logic ALL)
(set-option :incremental true)
(assert (> (arcsec real.pi) (/ 590 1)))
(check-sat)
