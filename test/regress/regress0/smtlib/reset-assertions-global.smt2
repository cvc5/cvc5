; EXPECT: unsat
; EXPECT: sat
; EXPECT: unsat
(set-option :global-declarations true)
(set-logic QF_BV)
(set-option :incremental true)
(declare-fun x2 () (_ BitVec 3))
(declare-fun x1 () (_ BitVec 3))
(declare-fun x0 () (_ BitVec 3))
(assert (bvult (bvudiv (bvudiv (bvudiv x0 x0) x1) x2) x1))
(assert (= #b000 x2))
(check-sat)
(reset-assertions)
(assert (= x2 x1))
(check-sat)
(reset-assertions)
(assert (distinct x1 x1))
(check-sat)
