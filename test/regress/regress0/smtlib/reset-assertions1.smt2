; EXPECT: unsat
; EXPECT: sat
(set-option :global-declarations true)
(set-logic QF_BV)
(declare-fun v0 () (_ BitVec 4))
(set-option :produce-models true)
(reset-assertions)
(set-option :incremental true)
(assert (and (= v0 (_ bv0 4)) (distinct v0 (_ bv0 4))))
(check-sat)
(reset-assertions)
(check-sat)
