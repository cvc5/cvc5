; EXPECT: (error "cannot get unsat core unless in unsat mode.")
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT: (error "Expected result unsat but got sat")
; EXIT: 1
(set-option :incremental true)
(set-option :produce-unsat-cores true)
(set-logic QF_BV)
(set-info :status unsat)
(get-unsat-core)
(set-info :status sat)
(check-sat)
(set-info :status sat)
(check-sat)
(push)
(assert false)
(check-sat)
(pop)
(set-info :status unsat)
(check-sat)
