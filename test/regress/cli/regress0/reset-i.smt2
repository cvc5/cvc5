; EXPECT: sat
; EXPECT: (error "Cannot make multiple queries unless incremental solving is enabled (try --incremental)")
; EXIT: 1
(reset)
(set-logic ALL)
(check-sat)
(check-sat)
