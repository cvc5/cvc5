; COMMAND-LINE: --incremental
; EXPECT: sat
; EXPECT: (error "cannot get value unless after a SAT or UNKNOWN response.")
; EXPECT: sat
; EXPECT: ((c #b1111))
(set-option :produce-models true)
(set-option :global-declarations true)
(set-logic QF_BV)
(check-sat)
(define-fun c () (_ BitVec 4) #b1111)
(get-value (c))
(check-sat)
(get-value (c))
