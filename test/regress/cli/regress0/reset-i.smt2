; EXPECT: sat
; EXPECT: (error "Cannot make multiple queries unless incremental solving is enabled (try --incremental)")
(set-logic ALL)
(reset)
(check-sat)
(check-sat)
