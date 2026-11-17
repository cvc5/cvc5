; The testers below enable unsat cores or proofs, in which case get-unsat-core
; is available.
; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; DISABLE-TESTER: alethe
; DISABLE-TESTER: cpc
; DISABLE-TESTER: cpc-logos
; EXPECT: unsat
; EXPECT: (a)
; EXPECT: (error "cannot get unsat core unless explicitly enabled (try --produce-unsat-cores)")
; EXIT: 1
(set-option :produce-unsat-assumptions true)
(set-logic QF_LIA)
(declare-fun x () Int)
(declare-fun a () Bool)
(assert (=> a (> x 5)))
(assert (< x 3))
(check-sat-assuming (a))
(get-unsat-assumptions)
(get-unsat-core)
