; EXPECT: unsat
(set-info :smt-lib-version 2.6)
(set-logic QF_BV)
(set-info :status unsat)

(declare-const x (_ BitVec 5))
(assert (not (=
	(bvudiv x #b01000)
	(concat #b000 ((_ extract 4 3) x)))))
(check-sat)
(exit)
