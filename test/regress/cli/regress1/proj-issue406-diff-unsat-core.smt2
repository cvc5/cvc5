; DISABLE-TESTER: unsat-core
; DISABLE-TESTER: proof
; EXPECT: unsat
; EXPECT: (error "Cannot get unsat core unless explicitly enabled (try --produce-unsat-cores)")
; EXIT: 1
(set-logic ALL)
(set-option :global-declarations true)
(set-option :produce-difficulty true)
(declare-const _x0 String)
(assert (let ((_let0 (str.suffixof _x0 _x0)))(and (and (not _let0) (= _let0 _let0)) _let0)))
(check-sat)
(get-unsat-core)