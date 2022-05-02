; EXPECT: sat
; EXPECT: unsat
; EXPECT: (
; EXPECT: )
(set-logic ALL)
(set-option :incremental true)
(set-option :produce-unsat-assumptions true)
(set-option :produce-unsat-cores true)
(check-sat)
(reset-assertions)
(assert false)
(check-sat)
(get-unsat-core)
