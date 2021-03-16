; SCRUBBER: sed 's/".*"/""/g'
; EXPECT: success
; EXPECT: success
; EXPECT: success
; EXPECT: success
; EXPECT: success
; EXPECT: success
; EXPECT: success
; EXPECT: (error "")
; EXPECT: (error "")
; EXPECT: (error "")
; EXPECT: (error "")
; EXPECT: success
; EXPECT: sat
(set-option :print-success true)
(set-option :produce-unsat-cores true)
(set-option :produce-models true)
(set-option :produce-proofs true)
(set-option :produce-assignments true)
(set-logic UF)
(declare-fun p () Bool)
(get-unsat-core)
(get-value (p))
(get-model)
(get-assignment)
(assert true)
(check-sat)
