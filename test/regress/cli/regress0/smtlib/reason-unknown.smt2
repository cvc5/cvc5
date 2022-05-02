; EXPECT: (error "Can't get-info :reason-unknown when the last result wasn't unknown!")
; EXPECT: sat
(set-logic QF_SAT)
(get-info :reason-unknown)
(check-sat)
