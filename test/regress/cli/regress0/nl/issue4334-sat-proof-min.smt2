; COMMAND-LINE: -i -q
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
; EXPECT: sat
(set-option :produce-unsat-cores true)
(assert (distinct 0 (mod 0 0)))
(check-sat)
(check-sat)
(check-sat)
(check-sat)