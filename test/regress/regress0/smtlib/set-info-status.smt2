; EXPECT: (error "Cannot get unsat core unless in unsat mode.")
; EXPECT: sat
; EXPECT: sat
; EXPECT: unsat
; EXPECT-ERROR: Expected result unsat but got sat
; ERROR-SCRUBBER: sed -e '/Fatal failure within.*/d'
; EXIT: -6
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
