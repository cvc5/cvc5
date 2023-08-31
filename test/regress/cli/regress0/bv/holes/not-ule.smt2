; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 4))
(declare-const y (_ BitVec 4))
(assert (not (=
  (not (bvule x y))
  (bvult y x)
	)))
(check-sat)
(exit)
