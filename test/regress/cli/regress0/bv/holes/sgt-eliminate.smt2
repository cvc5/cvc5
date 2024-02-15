; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 10))
(declare-const y (_ BitVec 10))
(assert (not (=
	(bvsgt x y)
	(bvslt y x)
	)))
(check-sat)
(exit)
